import NetHack.Soko22Hazard87.AndIntroBlocks0087
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro22000 (p : Pattern) (ha : d8825 p = 1) (hb : d122306 p = 1) : d124553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6957 q = 1) (hb : d122306 q = 1) : d124519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21983 q ha hb
    | true =>
      simp only [d6957, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d122306 q = 1) : d124520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21966 q ha hb
    | true =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8789 q = 1) (hb : d122306 q = 1) : d124525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8789, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8789, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8790 q = 1) (hb : d122306 q = 1) : d124526 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8790, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8790, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8791 q = 1) (hb : d122306 q = 1) : d124527 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8791, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8791, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8825 q = 1) (hb : d122306 q = 1) : d124553 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8825, d124553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8825, d124553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22001 (p : Pattern) (ha : d8830 p = 1) (hb : d122306 p = 1) : d124556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d122306 q = 1) : d124454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21977 q ha hb
    | true =>
      simp only [d8744, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d122306 q = 1) : d124455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d122306 q = 1) : d124531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8806 q = 1) (hb : d122306 q = 1) : d124532 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8806, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8807 q = 1) (hb : d122306 q = 1) : d124533 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8807, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8830 q = 1) (hb : d122306 q = 1) : d124556 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8830, d124556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8830, d124556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22002 (p : Pattern) (ha : d94354 p = 1) (hb : d122306 p = 1) : d124562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8770 q = 1) (hb : d122306 q = 1) : d124491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8770, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21988 q ha hb
    | true =>
      simp only [d8770, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21986 q ha hb
  have h2 (q : Pattern) (ha : d8771 q = 1) (hb : d122306 q = 1) : d124492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8771, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8771, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8772 q = 1) (hb : d122306 q = 1) : d124493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8772, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8772, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8773 q = 1) (hb : d122306 q = 1) : d124494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8773, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8773, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8777 q = 1) (hb : d122306 q = 1) : d124501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8777, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21989 q ha hb
    | true =>
      simp only [d8777, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21987 q ha hb
  have h6 (q : Pattern) (ha : d8778 q = 1) (hb : d122306 q = 1) : d124502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8778, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8778, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8779 q = 1) (hb : d122306 q = 1) : d124503 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8779, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8779, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8793 q = 1) (hb : d122306 q = 1) : d124529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8793, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21992 q ha hb
    | true =>
      simp only [d8793, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21984 q ha hb
  have h9 (q : Pattern) (ha : d94345 q = 1) (hb : d122306 q = 1) : d124530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94345, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8809 q = 1) (hb : d122306 q = 1) : d124535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21993 q ha hb
    | true =>
      simp only [d8809, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8810 q = 1) (hb : d122306 q = 1) : d124536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8810, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94346 q = 1) (hb : d122306 q = 1) : d124537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94346, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94347 q = 1) (hb : d122306 q = 1) : d124538 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94347, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94348 q = 1) (hb : d122306 q = 1) : d124539 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94348, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8816 q = 1) (hb : d122306 q = 1) : d124543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8816, d124543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21997 q ha hb
    | true =>
      simp only [d8816, d124543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21995 q ha hb
  have h16 (q : Pattern) (ha : d8817 q = 1) (hb : d122306 q = 1) : d124544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8817, d124544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8817, d124544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8818 q = 1) (hb : d122306 q = 1) : d124545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8818, d124545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8818, d124545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8819 q = 1) (hb : d122306 q = 1) : d124546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8819, d124546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8819, d124546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8821 q = 1) (hb : d122306 q = 1) : d124549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8821, d124549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21998 q ha hb
    | true =>
      simp only [d8821, d124549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21996 q ha hb
  have h20 (q : Pattern) (ha : d8822 q = 1) (hb : d122306 q = 1) : d124550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8822, d124550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8822, d124550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8823 q = 1) (hb : d122306 q = 1) : d124551 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8823, d124551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8823, d124551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8826 q = 1) (hb : d122306 q = 1) : d124554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21999 q ha hb
    | true =>
      simp only [d8826, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22000 q ha hb
  have h23 (q : Pattern) (ha : d94350 q = 1) (hb : d122306 q = 1) : d124555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94350, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8831 q = 1) (hb : d122306 q = 1) : d124557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22001 q ha hb
    | true =>
      simp only [d8831, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8832 q = 1) (hb : d122306 q = 1) : d124558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8832, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94351 q = 1) (hb : d122306 q = 1) : d124559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94351, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94352 q = 1) (hb : d122306 q = 1) : d124560 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94352, d124560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94352, d124560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94353 q = 1) (hb : d122306 q = 1) : d124561 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94353, d124561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94353, d124561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94354 q = 1) (hb : d122306 q = 1) : d124562 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94354, d124562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94354, d124562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro22003 (p : Pattern) (ha : d94361 p = 1) (hb : d122306 p = 1) : d124587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8826 q = 1) (hb : d122306 q = 1) : d124554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8826, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21999 q ha hb
    | true =>
      simp only [d8826, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22000 q ha hb
  have h2 (q : Pattern) (ha : d94350 q = 1) (hb : d122306 q = 1) : d124555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94350, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8831 q = 1) (hb : d122306 q = 1) : d124557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22001 q ha hb
    | true =>
      simp only [d8831, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8832 q = 1) (hb : d122306 q = 1) : d124558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8832, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94351 q = 1) (hb : d122306 q = 1) : d124559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94351, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94359 q = 1) (hb : d122306 q = 1) : d124585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94359, d124585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94359, d124585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94360 q = 1) (hb : d122306 q = 1) : d124586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94360, d124586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94360, d124586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94361 q = 1) (hb : d122306 q = 1) : d124587 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94361, d124587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94361, d124587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22004 (p : Pattern) (ha : d1396 p = 1) (hb : d122305 p = 1) : d124596 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1383 q = 1) : d1383 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1388 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1389 q = 1) (hb : d122304 q = 1) : d14993 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d122304, d14993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1389, d122304, d14993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1395 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1396 q = 1) (hb : d122305 q = 1) : d124596 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1396, d122305, d124596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1396, d122305, d124596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22005 (p : Pattern) (ha : d6349 p = 1) (hb : d122305 p = 1) : d124601 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1388 q = 1) : d1388 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1395 q = 1) (hb : d122304 q = 1) : d15014 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d122304, d15014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1395, d122304, d15014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6349 q = 1) (hb : d122305 q = 1) : d124601 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6349, d122305, d124601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6349, d122305, d124601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro22006 (p : Pattern) (ha : d7002 p = 1) (hb : d122306 p = 1) : d124615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1402 q = 1) (hb : d122305 q = 1) : d124602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22004 q ha hb
    | true =>
      simp only [d1402, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21971 q ha hb
  have h2 (q : Pattern) (ha : d1403 q = 1) (hb : d122305 q = 1) : d124603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1404 q = 1) (hb : d122305 q = 1) : d124604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7000 q = 1) (hb : d122306 q = 1) : d124605 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7000, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6355 q = 1) (hb : d122305 q = 1) : d6355 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6356 q = 1) (hb : d122305 q = 1) : d124610 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22005 q ha hb
    | true =>
      simp only [d6356, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6357 q = 1) (hb : d122305 q = 1) : d124611 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6358 q = 1) (hb : d122305 q = 1) : d124612 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6359 q = 1) (hb : d122306 q = 1) : d124613 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d122306, d124613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6359, d122306, d124613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d7001 q = 1) (hb : d122306 q = 1) : d124614 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7001, d124614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7001, d124614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7002 q = 1) (hb : d122306 q = 1) : d124615 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7002, d124615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7002, d124615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro22007 (p : Pattern) (ha : d1390 p = 1) (hb : d122305 p = 1) : d124595 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1379 q = 1) : d1379 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1383 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1384 q = 1) (hb : d122304 q = 1) : d14986 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1384, d122304, d14986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1384, d122304, d14986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1389 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1390 q = 1) (hb : d122305 q = 1) : d124595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1390, d122305, d124595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1390, d122305, d124595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22008 (p : Pattern) (ha : d8858 p = 1) (hb : d122306 p = 1) : d124607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1397 q = 1) (hb : d122305 q = 1) : d124597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d124597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22007 q ha hb
    | true =>
      simp only [d1397, d124597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22004 q ha hb
  have h2 (q : Pattern) (ha : d1398 q = 1) (hb : d122305 q = 1) : d124598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d124598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1398, d124598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1399 q = 1) (hb : d122305 q = 1) : d124599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d124599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1399, d124599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8856 q = 1) (hb : d122306 q = 1) : d124600 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8856, d122306, d124600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8856, d122306, d124600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1402 q = 1) (hb : d122305 q = 1) : d124602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22004 q ha hb
    | true =>
      simp only [d1402, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21971 q ha hb
  have h7 (q : Pattern) (ha : d1403 q = 1) (hb : d122305 q = 1) : d124603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1404 q = 1) (hb : d122305 q = 1) : d124604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7000 q = 1) (hb : d122306 q = 1) : d124605 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7000, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8857 q = 1) (hb : d122306 q = 1) : d124606 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8857, d124606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8857, d124606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8858 q = 1) (hb : d122306 q = 1) : d124607 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8858, d124607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8858, d124607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro22009 (p : Pattern) (ha : d8864 p = 1) (hb : d122306 p = 1) : d124621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8859 q = 1) (hb : d122306 q = 1) : d124608 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8859, d124608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22008 q ha hb
    | true =>
      simp only [d8859, d124608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8860 q = 1) (hb : d122306 q = 1) : d124609 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8860, d124609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8860, d124609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7003 q = 1) (hb : d122306 q = 1) : d124616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22006 q ha hb
    | true =>
      simp only [d7003, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7004 q = 1) (hb : d122306 q = 1) : d124617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8861 q = 1) (hb : d122306 q = 1) : d124618 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8861, d124618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8861, d124618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8862 q = 1) (hb : d122306 q = 1) : d124619 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8862, d124619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8862, d124619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8863 q = 1) (hb : d122306 q = 1) : d124620 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8863, d124620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8863, d124620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8864 q = 1) (hb : d122306 q = 1) : d124621 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8864, d124621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8864, d124621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22010 (p : Pattern) (ha : d8868 p = 1) (hb : d122306 p = 1) : d124633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7003 q = 1) (hb : d122306 q = 1) : d124616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22006 q ha hb
    | true =>
      simp only [d7003, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7004 q = 1) (hb : d122306 q = 1) : d124617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d122306 q = 1) : d124628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21973 q ha hb
    | true =>
      simp only [d1431, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d122306 q = 1) : d124629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8865 q = 1) (hb : d122306 q = 1) : d124630 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8865, d124630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8865, d124630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8866 q = 1) (hb : d122306 q = 1) : d124631 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8866, d124631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8866, d124631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8867 q = 1) (hb : d122306 q = 1) : d124632 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8867, d124632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8867, d124632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8868 q = 1) (hb : d122306 q = 1) : d124633 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8868, d124633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8868, d124633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22011 (p : Pattern) (ha : d8882 p = 1) (hb : d122306 p = 1) : d124637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1402 q = 1) (hb : d122305 q = 1) : d124602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22004 q ha hb
    | true =>
      simp only [d1402, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21971 q ha hb
  have h2 (q : Pattern) (ha : d1403 q = 1) (hb : d122305 q = 1) : d124603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1404 q = 1) (hb : d122305 q = 1) : d124604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7000 q = 1) (hb : d122306 q = 1) : d124605 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7000, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1412 q = 1) (hb : d122305 q = 1) : d124622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21971 q ha hb
    | true =>
      simp only [d1412, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21972 q ha hb
  have h7 (q : Pattern) (ha : d1413 q = 1) (hb : d122305 q = 1) : d124623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1414 q = 1) (hb : d122305 q = 1) : d124624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1420 q = 1) (hb : d122306 q = 1) : d124625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d122306, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1420, d122306, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8881 q = 1) (hb : d122306 q = 1) : d124636 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8881, d124636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8881, d124636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8882 q = 1) (hb : d122306 q = 1) : d124637 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8882, d124637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8882, d124637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro22012 (p : Pattern) (ha : d8888 p = 1) (hb : d122306 p = 1) : d124643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8883 q = 1) (hb : d122306 q = 1) : d124638 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8883, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22011 q ha hb
    | true =>
      simp only [d8883, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d122306 q = 1) : d124639 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8885 q = 1) (hb : d122306 q = 1) : d124640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8885, d124640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8885, d124640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8886 q = 1) (hb : d122306 q = 1) : d124641 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8886, d124641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8886, d124641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8887 q = 1) (hb : d122306 q = 1) : d124642 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8887, d124642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8887, d124642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8888 q = 1) (hb : d122306 q = 1) : d124643 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8888, d124643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8888, d124643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22013 (p : Pattern) (ha : d94371 p = 1) (hb : d122306 p = 1) : d124649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8869 q = 1) (hb : d122306 q = 1) : d124634 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8869, d124634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22009 q ha hb
    | true =>
      simp only [d8869, d124634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22010 q ha hb
  have h2 (q : Pattern) (ha : d94367 q = 1) (hb : d122306 q = 1) : d124635 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94367, d124635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94367, d124635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8889 q = 1) (hb : d122306 q = 1) : d124644 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8889, d124644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22012 q ha hb
    | true =>
      simp only [d8889, d124644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8890 q = 1) (hb : d122306 q = 1) : d124645 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8890, d124645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8890, d124645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94368 q = 1) (hb : d122306 q = 1) : d124646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94368, d124646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94368, d124646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94369 q = 1) (hb : d122306 q = 1) : d124647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94369, d124647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94369, d124647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94370 q = 1) (hb : d122306 q = 1) : d124648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94370, d124648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94370, d124648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94371 q = 1) (hb : d122306 q = 1) : d124649 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94371, d124649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94371, d124649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22014 (p : Pattern) (ha : d94377 p = 1) (hb : d122306 p = 1) : d124666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8756 q = 1) (hb : d122306 q = 1) : d124474 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8756, d124474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8756, d124474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21979 q ha hb
  have h2 (q : Pattern) (ha : d8757 q = 1) (hb : d122306 q = 1) : d124475 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8757, d124475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8757, d124475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8765 q = 1) (hb : d122306 q = 1) : d124484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21979 q ha hb
    | true =>
      simp only [d8765, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21981 q ha hb
  have h4 (q : Pattern) (ha : d8766 q = 1) (hb : d122306 q = 1) : d124485 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8766, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8767 q = 1) (hb : d122306 q = 1) : d124486 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8767, d124486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8767, d124486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94355 q = 1) (hb : d122306 q = 1) : d124563 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94355, d124563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21994 q ha hb
    | true =>
      simp only [d94355, d124563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22002 q ha hb
  have h7 (q : Pattern) (ha : d8844 q = 1) (hb : d122306 q = 1) : d124581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8844, d124581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21985 q ha hb
    | true =>
      simp only [d8844, d124581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21969 q ha hb
  have h8 (q : Pattern) (ha : d94356 q = 1) (hb : d122306 q = 1) : d124582 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94356, d124582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94356, d124582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94357 q = 1) (hb : d122306 q = 1) : d124583 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94357, d124583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94357, d124583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94358 q = 1) (hb : d122306 q = 1) : d124584 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94358, d124584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94358, d124584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94362 q = 1) (hb : d122306 q = 1) : d124588 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94362, d124588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94362, d124588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22003 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d122306 q = 1) : d124590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d124590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d124590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21970 q ha hb
  have h13 (q : Pattern) (ha : d94363 q = 1) (hb : d122306 q = 1) : d124591 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94363, d124591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94363, d124591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94364 q = 1) (hb : d122306 q = 1) : d124592 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94364, d124592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94364, d124592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94365 q = 1) (hb : d122306 q = 1) : d124593 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94365, d124593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94365, d124593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94366 q = 1) (hb : d122306 q = 1) : d124594 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94366, d124594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94366, d124594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94372 q = 1) (hb : d122306 q = 1) : d124650 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94372, d124650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94372, d124650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22013 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d122306 q = 1) : d124661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d124661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d124661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21975 q ha hb
  have h19 (q : Pattern) (ha : d94373 q = 1) (hb : d122306 q = 1) : d124662 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94373, d124662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94373, d124662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94374 q = 1) (hb : d122306 q = 1) : d124663 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94374, d124663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94374, d124663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94375 q = 1) (hb : d122306 q = 1) : d124664 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94375, d124664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94375, d124664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94376 q = 1) (hb : d122306 q = 1) : d124665 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94376, d124665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94376, d124665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94377 q = 1) (hb : d122306 q = 1) : d124666 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94377, d124666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94377, d124666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro22015 (p : Pattern) (ha : d94383 p = 1) (hb : d122306 p = 1) : d124672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94378 q = 1) (hb : d122306 q = 1) : d124667 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94378, d124667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94378, d124667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22014 q ha hb
  have h2 (q : Pattern) (ha : d94379 q = 1) (hb : d122306 q = 1) : d124668 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94379, d124668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94379, d124668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94380 q = 1) (hb : d122306 q = 1) : d124669 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94380, d124669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94380, d124669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94381 q = 1) (hb : d122306 q = 1) : d124670 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94381, d124670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94381, d124670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94382 q = 1) (hb : d122306 q = 1) : d124671 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94382, d124671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94382, d124671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94383 q = 1) (hb : d122306 q = 1) : d124672 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94383, d124672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94383, d124672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22016 (p : Pattern) (ha : d1589 p = 1) (hb : d122305 p = 1) : d124677 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1573 q = 1) : d1573 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1585 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1586 q = 1) (hb : d122304 q = 1) : d15155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d122304, d15155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1586, d122304, d15155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1588 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1589 q = 1) (hb : d122305 q = 1) : d124677 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1589, d122305, d124677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1589, d122305, d124677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22017 (p : Pattern) (ha : d1602 p = 1) (hb : d122305 p = 1) : d13287 p = 1 := by
  have h0 (q : Pattern) (ha : d1588 q = 1) (hb : d122304 q = 1) : d1588 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1601 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1602 q = 1) (hb : d122305 q = 1) : d13287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1602, d122305, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1602, d122305, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro22018 (p : Pattern) (ha : d1613 p = 1) (hb : d122306 p = 1) : d124691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1603 q = 1) (hb : d122305 q = 1) : d124682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22016 q ha hb
    | true =>
      simp only [d1603, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22017 q ha hb
  have h2 (q : Pattern) (ha : d1604 q = 1) (hb : d122305 q = 1) : d124683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1605 q = 1) (hb : d122305 q = 1) : d124684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1607 q = 1) (hb : d122306 q = 1) : d124685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d122306, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1607, d122306, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1612 q = 1) (hb : d122306 q = 1) : d124690 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1612, d124690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1612, d124690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1613 q = 1) (hb : d122306 q = 1) : d124691 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1613, d124691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1613, d124691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro22019 (p : Pattern) (ha : d1623 p = 1) (hb : d122306 p = 1) : d124701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d122306 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d122306 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d122306 q = 1) : d124700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1623 q = 1) (hb : d122306 q = 1) : d124701 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, d124701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, d124701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22020 (p : Pattern) (ha : d1633 p = 1) (hb : d122306 p = 1) : d124711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d122306 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d122306 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d122306 q = 1) : d124700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1633 q = 1) (hb : d122306 q = 1) : d124711 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, d124711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1633, d124711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22021 (p : Pattern) (ha : d1838 p = 1) (hb : d122306 p = 1) : d124814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d122306 q = 1) : d124803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22019 q ha hb
    | true =>
      simp only [d1827, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d122306 q = 1) : d124804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d122306 q = 1) : d124805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d122306 q = 1) : d124806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d122306 q = 1) : d124807 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1833 q = 1) (hb : d122306 q = 1) : d124809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22020 q ha hb
    | true =>
      simp only [d1833, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1834 q = 1) (hb : d122306 q = 1) : d124810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1835 q = 1) (hb : d122306 q = 1) : d124811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1835, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1836 q = 1) (hb : d122306 q = 1) : d124812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1837 q = 1) (hb : d122306 q = 1) : d124813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1838 q = 1) (hb : d122306 q = 1) : d124814 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, d124814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1838, d124814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22022 (p : Pattern) (ha : d1847 p = 1) (hb : d122306 p = 1) : d124823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1833 q = 1) (hb : d122306 q = 1) : d124809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22020 q ha hb
    | true =>
      simp only [d1833, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1834 q = 1) (hb : d122306 q = 1) : d124810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1835 q = 1) (hb : d122306 q = 1) : d124811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1835, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1836 q = 1) (hb : d122306 q = 1) : d124812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1837 q = 1) (hb : d122306 q = 1) : d124813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1847 q = 1) (hb : d122306 q = 1) : d124823 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, d124823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, d124823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22023 (p : Pattern) (ha : d1878 p = 1) (hb : d122305 p = 1) : d124835 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1865 q = 1) : d1865 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1871 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1872 q = 1) (hb : d122304 q = 1) : d15407 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d122304, d15407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1872, d122304, d15407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1877 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1878 q = 1) (hb : d122305 q = 1) : d124835 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1878, d122305, d124835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1878, d122305, d124835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22024 (p : Pattern) (ha : d1888 p = 1) (hb : d122305 p = 1) : d13516 p = 1 := by
  have h0 (q : Pattern) (ha : d1877 q = 1) (hb : d122304 q = 1) : d1877 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1887 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1888 q = 1) (hb : d122305 q = 1) : d13516 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1888, d122305, d13516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1888, d122305, d13516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro22025 (p : Pattern) (ha : d1907 p = 1) (hb : d122306 p = 1) : d124861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1889 q = 1) (hb : d122305 q = 1) : d124856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22023 q ha hb
    | true =>
      simp only [d1889, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22024 q ha hb
  have h2 (q : Pattern) (ha : d1890 q = 1) (hb : d122305 q = 1) : d124857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1891 q = 1) (hb : d122305 q = 1) : d124858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1897 q = 1) (hb : d122306 q = 1) : d124859 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d122306, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1897, d122306, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1906 q = 1) (hb : d122306 q = 1) : d124860 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1906, d124860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1906, d124860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1907 q = 1) (hb : d122306 q = 1) : d124861 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1907, d124861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1907, d124861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro22026 (p : Pattern) (ha : d1974 p = 1) (hb : d122306 p = 1) : d124888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1908 q = 1) (hb : d122306 q = 1) : d124862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22025 q ha hb
    | true =>
      simp only [d1908, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1909 q = 1) (hb : d122306 q = 1) : d124863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1971 q = 1) (hb : d122306 q = 1) : d124885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, d124885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1971, d124885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1972 q = 1) (hb : d122306 q = 1) : d124886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, d124886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1972, d124886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1973 q = 1) (hb : d122306 q = 1) : d124887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, d124887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1973, d124887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1974 q = 1) (hb : d122306 q = 1) : d124888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, d124888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1974, d124888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22027 (p : Pattern) (ha : d1980 p = 1) (hb : d122306 p = 1) : d124894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1975 q = 1) (hb : d122306 q = 1) : d124889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, d124889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22026 q ha hb
    | true =>
      simp only [d1975, d124889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1976 q = 1) (hb : d122306 q = 1) : d124890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, d124890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1976, d124890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1977 q = 1) (hb : d122306 q = 1) : d124891 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, d124891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1977, d124891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1978 q = 1) (hb : d122306 q = 1) : d124892 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, d124892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, d124892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1979 q = 1) (hb : d122306 q = 1) : d124893 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, d124893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, d124893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1980 q = 1) (hb : d122306 q = 1) : d124894 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, d124894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, d124894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22028 (p : Pattern) (ha : d1587 p = 1) (hb : d122305 p = 1) : d124676 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1558 q = 1) : d1558 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1573 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1574 q = 1) (hb : d122304 q = 1) : d15150 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, d122304, d15150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1574, d122304, d15150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1586 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1587 q = 1) (hb : d122305 q = 1) : d124676 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1587, d122305, d124676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1587, d122305, d124676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22029 (p : Pattern) (ha : d8911 p = 1) (hb : d122306 p = 1) : d124687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1590 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22028 q ha hb
    | true =>
      simp only [d1590, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22016 q ha hb
  have h2 (q : Pattern) (ha : d1591 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1592 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7034 q = 1) (hb : d122306 q = 1) : d124681 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7034, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1603 q = 1) (hb : d122305 q = 1) : d124682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22016 q ha hb
    | true =>
      simp only [d1603, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22017 q ha hb
  have h7 (q : Pattern) (ha : d1604 q = 1) (hb : d122305 q = 1) : d124683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1605 q = 1) (hb : d122305 q = 1) : d124684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1607 q = 1) (hb : d122306 q = 1) : d124685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d122306, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1607, d122306, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8910 q = 1) (hb : d122306 q = 1) : d124686 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8910, d124686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8910, d124686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8911 q = 1) (hb : d122306 q = 1) : d124687 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8911, d124687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8911, d124687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro22030 (p : Pattern) (ha : d8917 p = 1) (hb : d122306 p = 1) : d124697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22029 q ha hb
    | true =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d122306 q = 1) : d124694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d122306 q = 1) : d124695 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8916 q = 1) (hb : d122306 q = 1) : d124696 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8916, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8917 q = 1) (hb : d122306 q = 1) : d124697 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8917, d124697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8917, d124697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22031 (p : Pattern) (ha : d8923 p = 1) (hb : d122306 p = 1) : d124707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8918 q = 1) (hb : d122306 q = 1) : d124702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22030 q ha hb
    | true =>
      simp only [d8918, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22019 q ha hb
  have h2 (q : Pattern) (ha : d8919 q = 1) (hb : d122306 q = 1) : d124703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8920 q = 1) (hb : d122306 q = 1) : d124704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8920, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8921 q = 1) (hb : d122306 q = 1) : d124705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8922 q = 1) (hb : d122306 q = 1) : d124706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8923 q = 1) (hb : d122306 q = 1) : d124707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8923, d124707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8923, d124707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22032 (p : Pattern) (ha : d8926 p = 1) (hb : d122306 p = 1) : d124710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22029 q ha hb
    | true =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d122306 q = 1) : d124694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d122306 q = 1) : d124695 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8916 q = 1) (hb : d122306 q = 1) : d124696 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8916, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8916, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8926 q = 1) (hb : d122306 q = 1) : d124710 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8926, d124710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8926, d124710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22033 (p : Pattern) (ha : d8932 p = 1) (hb : d122306 p = 1) : d124717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8918 q = 1) (hb : d122306 q = 1) : d124702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8918, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22030 q ha hb
    | true =>
      simp only [d8918, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22019 q ha hb
  have h2 (q : Pattern) (ha : d8919 q = 1) (hb : d122306 q = 1) : d124703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8919, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8919, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8920 q = 1) (hb : d122306 q = 1) : d124704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8920, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8920, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8921 q = 1) (hb : d122306 q = 1) : d124705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8921, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8921, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8922 q = 1) (hb : d122306 q = 1) : d124706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8922, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8922, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8927 q = 1) (hb : d122306 q = 1) : d124712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22032 q ha hb
    | true =>
      simp only [d8927, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22020 q ha hb
  have h7 (q : Pattern) (ha : d8928 q = 1) (hb : d122306 q = 1) : d124713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8928, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8929 q = 1) (hb : d122306 q = 1) : d124714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8929, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8930 q = 1) (hb : d122306 q = 1) : d124715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8931 q = 1) (hb : d122306 q = 1) : d124716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8932 q = 1) (hb : d122306 q = 1) : d124717 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8932, d124717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8932, d124717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22034 (p : Pattern) (ha : d5120 p = 1) (hb : d122305 p = 1) : d124677 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1573 q = 1) : d1573 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1585 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1586 q = 1) (hb : d122304 q = 1) : d15155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d122304, d15155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1586, d122304, d15155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5120 q = 1) (hb : d122305 q = 1) : d124677 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5120, d122305, d124677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5120, d122305, d124677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro22035 (p : Pattern) (ha : d7036 p = 1) (hb : d122306 p = 1) : d124752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1590 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22028 q ha hb
    | true =>
      simp only [d1590, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22016 q ha hb
  have h2 (q : Pattern) (ha : d1591 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1592 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7034 q = 1) (hb : d122306 q = 1) : d124681 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7034, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5139 q = 1) (hb : d122305 q = 1) : d5139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5140 q = 1) (hb : d122305 q = 1) : d124747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22034 q ha hb
    | true =>
      simp only [d5140, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5141 q = 1) (hb : d122305 q = 1) : d124748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5142 q = 1) (hb : d122305 q = 1) : d124749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5143 q = 1) (hb : d122306 q = 1) : d124750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d122306, d124750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5143, d122306, d124750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d7035 q = 1) (hb : d122306 q = 1) : d124751 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7035, d124751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7035, d124751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7036 q = 1) (hb : d122306 q = 1) : d124752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7036, d124752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7036, d124752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro22036 (p : Pattern) (ha : d8960 p = 1) (hb : d122306 p = 1) : d124762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d122306 q = 1) : d124753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22035 q ha hb
    | true =>
      simp only [d7037, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d122306 q = 1) : d124754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8957 q = 1) (hb : d122306 q = 1) : d124759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8957, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8958 q = 1) (hb : d122306 q = 1) : d124760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8958, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8959 q = 1) (hb : d122306 q = 1) : d124761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8959, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8960 q = 1) (hb : d122306 q = 1) : d124762 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8960, d124762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8960, d124762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22037 (p : Pattern) (ha : d9011 p = 1) (hb : d122306 p = 1) : d124808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9006 q = 1) (hb : d122306 q = 1) : d124798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9006, d124798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22036 q ha hb
    | true =>
      simp only [d9006, d124798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22019 q ha hb
  have h2 (q : Pattern) (ha : d9007 q = 1) (hb : d122306 q = 1) : d124799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9007, d124799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9007, d124799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9008 q = 1) (hb : d122306 q = 1) : d124800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9008, d124800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9008, d124800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9009 q = 1) (hb : d122306 q = 1) : d124801 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9009, d124801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9009, d124801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9010 q = 1) (hb : d122306 q = 1) : d124802 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9010, d124802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9010, d124802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d122306 q = 1) : d124803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22019 q ha hb
    | true =>
      simp only [d1827, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d122306 q = 1) : d124804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d122306 q = 1) : d124805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d122306 q = 1) : d124806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d122306 q = 1) : d124807 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9011 q = 1) (hb : d122306 q = 1) : d124808 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9011, d124808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9011, d124808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22038 (p : Pattern) (ha : d1646 p = 1) (hb : d122306 p = 1) : d124724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d122306 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d122306 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d122306 q = 1) : d124723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1646 q = 1) (hb : d122306 q = 1) : d124724 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, d124724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, d124724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22039 (p : Pattern) (ha : d1656 p = 1) (hb : d122306 p = 1) : d124734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d122306 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d122306 q = 1) : d124732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d122306 q = 1) : d124733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d122306 q = 1) : d124734 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, d124734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, d124734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22040 (p : Pattern) (ha : d8937 p = 1) (hb : d122306 p = 1) : d124722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22029 q ha hb
    | true =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d122306 q = 1) : d124694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d122306 q = 1) : d124695 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8936 q = 1) (hb : d122306 q = 1) : d124721 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8937 q = 1) (hb : d122306 q = 1) : d124722 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8937, d124722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8937, d124722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22041 (p : Pattern) (ha : d8944 p = 1) (hb : d122306 p = 1) : d124731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22029 q ha hb
    | true =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d122306 q = 1) : d124694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8942 q = 1) (hb : d122306 q = 1) : d124729 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8943 q = 1) (hb : d122306 q = 1) : d124730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8943, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8944 q = 1) (hb : d122306 q = 1) : d124731 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8944, d124731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8944, d124731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22042 (p : Pattern) (ha : d1670 p = 1) (hb : d122305 p = 1) : d124738 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1668 q = 1) : d1668 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1558 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1669 q = 1) (hb : d122304 q = 1) : d15228 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1669, d122304, d15228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1669, d122304, d15228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1574 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1670 q = 1) (hb : d122305 q = 1) : d124738 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1670, d122305, d124738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1670, d122305, d124738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22043 (p : Pattern) (ha : d8950 p = 1) (hb : d122306 p = 1) : d124744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1671 q = 1) (hb : d122305 q = 1) : d124739 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, d124739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22042 q ha hb
    | true =>
      simp only [d1671, d124739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22028 q ha hb
  have h2 (q : Pattern) (ha : d1672 q = 1) (hb : d122305 q = 1) : d124740 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, d124740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1672, d124740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1673 q = 1) (hb : d122305 q = 1) : d124741 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, d124741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1673, d124741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8948 q = 1) (hb : d122306 q = 1) : d124742 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8948, d122306, d124742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8948, d122306, d124742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1590 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22028 q ha hb
    | true =>
      simp only [d1590, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22016 q ha hb
  have h7 (q : Pattern) (ha : d1591 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1592 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7034 q = 1) (hb : d122306 q = 1) : d124681 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7034, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8949 q = 1) (hb : d122306 q = 1) : d124743 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8949, d124743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8949, d124743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8950 q = 1) (hb : d122306 q = 1) : d124744 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8950, d124744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8950, d124744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro22044 (p : Pattern) (ha : d8956 p = 1) (hb : d122306 p = 1) : d124758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d122306 q = 1) : d124745 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22043 q ha hb
    | true =>
      simp only [d8951, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d122306 q = 1) : d124746 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7037 q = 1) (hb : d122306 q = 1) : d124753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22035 q ha hb
    | true =>
      simp only [d7037, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7038 q = 1) (hb : d122306 q = 1) : d124754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8953 q = 1) (hb : d122306 q = 1) : d124755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8953, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8954 q = 1) (hb : d122306 q = 1) : d124756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8954, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8955 q = 1) (hb : d122306 q = 1) : d124757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8955, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8956 q = 1) (hb : d122306 q = 1) : d124758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8956, d124758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8956, d124758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22045 (p : Pattern) (ha : d8976 p = 1) (hb : d122306 p = 1) : d124768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22029 q ha hb
    | true =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d122306 q = 1) : d124765 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d122306 q = 1) : d124766 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8975 q = 1) (hb : d122306 q = 1) : d124767 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8975, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8976 q = 1) (hb : d122306 q = 1) : d124768 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8976, d124768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8976, d124768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22046 (p : Pattern) (ha : d94391 p = 1) (hb : d122306 p = 1) : d124774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8938 q = 1) (hb : d122306 q = 1) : d124725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22040 q ha hb
    | true =>
      simp only [d8938, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22038 q ha hb
  have h2 (q : Pattern) (ha : d8939 q = 1) (hb : d122306 q = 1) : d124726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8940 q = 1) (hb : d122306 q = 1) : d124727 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8940, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8941 q = 1) (hb : d122306 q = 1) : d124728 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8945 q = 1) (hb : d122306 q = 1) : d124735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22041 q ha hb
    | true =>
      simp only [d8945, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22039 q ha hb
  have h6 (q : Pattern) (ha : d8946 q = 1) (hb : d122306 q = 1) : d124736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8947 q = 1) (hb : d122306 q = 1) : d124737 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8947, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8961 q = 1) (hb : d122306 q = 1) : d124763 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22044 q ha hb
    | true =>
      simp only [d8961, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22036 q ha hb
  have h9 (q : Pattern) (ha : d94387 q = 1) (hb : d122306 q = 1) : d124764 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94387, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8977 q = 1) (hb : d122306 q = 1) : d124769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22045 q ha hb
    | true =>
      simp only [d8977, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8978 q = 1) (hb : d122306 q = 1) : d124770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8978, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94388 q = 1) (hb : d122306 q = 1) : d124771 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94388, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94389 q = 1) (hb : d122306 q = 1) : d124772 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94389, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94390 q = 1) (hb : d122306 q = 1) : d124773 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94390, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94391 q = 1) (hb : d122306 q = 1) : d124774 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94391, d124774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94391, d124774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro22047 (p : Pattern) (ha : d1804 p = 1) (hb : d122306 p = 1) : d124776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d122306 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d122306 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d122306 q = 1) : d124723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1804 q = 1) (hb : d122306 q = 1) : d124776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, d124776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1804, d124776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22048 (p : Pattern) (ha : d1810 p = 1) (hb : d122306 p = 1) : d124782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d122306 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d122306 q = 1) : d124732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d122306 q = 1) : d124733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1810 q = 1) (hb : d122306 q = 1) : d124782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, d124782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1810, d124782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22049 (p : Pattern) (ha : d8983 p = 1) (hb : d122306 p = 1) : d124775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22029 q ha hb
    | true =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d122306 q = 1) : d124694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8915 q = 1) (hb : d122306 q = 1) : d124695 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8915, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8915, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8936 q = 1) (hb : d122306 q = 1) : d124721 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8936, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8936, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8983 q = 1) (hb : d122306 q = 1) : d124775 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8983, d124775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8983, d124775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22050 (p : Pattern) (ha : d8988 p = 1) (hb : d122306 p = 1) : d124781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22029 q ha hb
    | true =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8914 q = 1) (hb : d122306 q = 1) : d124694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8914, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8914, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8942 q = 1) (hb : d122306 q = 1) : d124729 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8942, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8942, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8943 q = 1) (hb : d122306 q = 1) : d124730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8943, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8943, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8988 q = 1) (hb : d122306 q = 1) : d124781 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8988, d124781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8988, d124781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22051 (p : Pattern) (ha : d8992 p = 1) (hb : d122306 p = 1) : d124786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d122306 q = 1) : d124745 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22043 q ha hb
    | true =>
      simp only [d8951, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d122306 q = 1) : d124746 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7037 q = 1) (hb : d122306 q = 1) : d124753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22035 q ha hb
    | true =>
      simp only [d7037, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7038 q = 1) (hb : d122306 q = 1) : d124754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8953 q = 1) (hb : d122306 q = 1) : d124755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8953, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8953, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8954 q = 1) (hb : d122306 q = 1) : d124756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8954, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8954, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8955 q = 1) (hb : d122306 q = 1) : d124757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8955, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8955, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8992 q = 1) (hb : d122306 q = 1) : d124786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8992, d124786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8992, d124786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22052 (p : Pattern) (ha : d8993 p = 1) (hb : d122306 p = 1) : d124787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7037 q = 1) (hb : d122306 q = 1) : d124753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22035 q ha hb
    | true =>
      simp only [d7037, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7038 q = 1) (hb : d122306 q = 1) : d124754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7038, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22018 q ha hb
    | true =>
      simp only [d1614, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8957 q = 1) (hb : d122306 q = 1) : d124759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8957, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8957, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8958 q = 1) (hb : d122306 q = 1) : d124760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8958, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8958, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8959 q = 1) (hb : d122306 q = 1) : d124761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8959, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8959, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8993 q = 1) (hb : d122306 q = 1) : d124787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8993, d124787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8993, d124787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22053 (p : Pattern) (ha : d8998 p = 1) (hb : d122306 p = 1) : d124790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22029 q ha hb
    | true =>
      simp only [d8912, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d122306 q = 1) : d124765 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d122306 q = 1) : d124766 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8975 q = 1) (hb : d122306 q = 1) : d124767 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8975, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8998 q = 1) (hb : d122306 q = 1) : d124790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8998, d124790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8998, d124790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22054 (p : Pattern) (ha : d94396 p = 1) (hb : d122306 p = 1) : d124796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8938 q = 1) (hb : d122306 q = 1) : d124725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8938, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22040 q ha hb
    | true =>
      simp only [d8938, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22038 q ha hb
  have h2 (q : Pattern) (ha : d8939 q = 1) (hb : d122306 q = 1) : d124726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8939, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8939, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8940 q = 1) (hb : d122306 q = 1) : d124727 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8940, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8940, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8941 q = 1) (hb : d122306 q = 1) : d124728 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8941, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8941, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8945 q = 1) (hb : d122306 q = 1) : d124735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8945, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22041 q ha hb
    | true =>
      simp only [d8945, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22039 q ha hb
  have h6 (q : Pattern) (ha : d8946 q = 1) (hb : d122306 q = 1) : d124736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8946, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8946, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8947 q = 1) (hb : d122306 q = 1) : d124737 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8947, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8947, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8961 q = 1) (hb : d122306 q = 1) : d124763 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8961, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22044 q ha hb
    | true =>
      simp only [d8961, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22036 q ha hb
  have h9 (q : Pattern) (ha : d94387 q = 1) (hb : d122306 q = 1) : d124764 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94387, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8977 q = 1) (hb : d122306 q = 1) : d124769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8977, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22045 q ha hb
    | true =>
      simp only [d8977, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8978 q = 1) (hb : d122306 q = 1) : d124770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8978, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8978, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94388 q = 1) (hb : d122306 q = 1) : d124771 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94388, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94389 q = 1) (hb : d122306 q = 1) : d124772 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94389, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94390 q = 1) (hb : d122306 q = 1) : d124773 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94390, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8984 q = 1) (hb : d122306 q = 1) : d124777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8984, d124777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22049 q ha hb
    | true =>
      simp only [d8984, d124777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22047 q ha hb
  have h16 (q : Pattern) (ha : d8985 q = 1) (hb : d122306 q = 1) : d124778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8985, d124778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8985, d124778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8986 q = 1) (hb : d122306 q = 1) : d124779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8986, d124779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8986, d124779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8987 q = 1) (hb : d122306 q = 1) : d124780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8987, d124780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8987, d124780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8989 q = 1) (hb : d122306 q = 1) : d124783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8989, d124783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22050 q ha hb
    | true =>
      simp only [d8989, d124783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22048 q ha hb
  have h20 (q : Pattern) (ha : d8990 q = 1) (hb : d122306 q = 1) : d124784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8990, d124784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8990, d124784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8991 q = 1) (hb : d122306 q = 1) : d124785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8991, d124785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8991, d124785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8994 q = 1) (hb : d122306 q = 1) : d124788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22051 q ha hb
    | true =>
      simp only [d8994, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22052 q ha hb
  have h23 (q : Pattern) (ha : d94392 q = 1) (hb : d122306 q = 1) : d124789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94392, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8999 q = 1) (hb : d122306 q = 1) : d124791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22053 q ha hb
    | true =>
      simp only [d8999, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9000 q = 1) (hb : d122306 q = 1) : d124792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9000, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94393 q = 1) (hb : d122306 q = 1) : d124793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94393, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94394 q = 1) (hb : d122306 q = 1) : d124794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94394, d124794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94394, d124794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94395 q = 1) (hb : d122306 q = 1) : d124795 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94395, d124795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94395, d124795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94396 q = 1) (hb : d122306 q = 1) : d124796 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94396, d124796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94396, d124796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro22055 (p : Pattern) (ha : d94403 p = 1) (hb : d122306 p = 1) : d124821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8994 q = 1) (hb : d122306 q = 1) : d124788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8994, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22051 q ha hb
    | true =>
      simp only [d8994, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22052 q ha hb
  have h2 (q : Pattern) (ha : d94392 q = 1) (hb : d122306 q = 1) : d124789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94392, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8999 q = 1) (hb : d122306 q = 1) : d124791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8999, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22053 q ha hb
    | true =>
      simp only [d8999, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9000 q = 1) (hb : d122306 q = 1) : d124792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9000, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9000, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94393 q = 1) (hb : d122306 q = 1) : d124793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94393, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94401 q = 1) (hb : d122306 q = 1) : d124819 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94401, d124819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94401, d124819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94402 q = 1) (hb : d122306 q = 1) : d124820 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94402, d124820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94402, d124820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94403 q = 1) (hb : d122306 q = 1) : d124821 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94403, d124821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94403, d124821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22056 (p : Pattern) (ha : d1873 p = 1) (hb : d122305 p = 1) : d124830 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1860 q = 1) : d1860 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1865 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1866 q = 1) (hb : d122304 q = 1) : d15386 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1866, d122304, d15386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1866, d122304, d15386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1872 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1873 q = 1) (hb : d122305 q = 1) : d124830 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1873, d122305, d124830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1873, d122305, d124830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22057 (p : Pattern) (ha : d6495 p = 1) (hb : d122305 p = 1) : d124835 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1865 q = 1) : d1865 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1871 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1872 q = 1) (hb : d122304 q = 1) : d15407 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d122304, d15407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1872, d122304, d15407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6495 q = 1) (hb : d122305 q = 1) : d124835 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6495, d122305, d124835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6495, d122305, d124835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro22058 (p : Pattern) (ha : d7082 p = 1) (hb : d122306 p = 1) : d124849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d122305 q = 1) : d124836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22056 q ha hb
    | true =>
      simp only [d1879, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22023 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d122305 q = 1) : d124837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d122305 q = 1) : d124838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7080 q = 1) (hb : d122306 q = 1) : d124839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7080, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6501 q = 1) (hb : d122305 q = 1) : d6501 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6502 q = 1) (hb : d122305 q = 1) : d124844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22057 q ha hb
    | true =>
      simp only [d6502, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6503 q = 1) (hb : d122305 q = 1) : d124845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6504 q = 1) (hb : d122305 q = 1) : d124846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6505 q = 1) (hb : d122306 q = 1) : d124847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d122306, d124847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6505, d122306, d124847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d7081 q = 1) (hb : d122306 q = 1) : d124848 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7081, d124848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7081, d124848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7082 q = 1) (hb : d122306 q = 1) : d124849 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7082, d124849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7082, d124849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro22059 (p : Pattern) (ha : d1867 p = 1) (hb : d122305 p = 1) : d124829 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1856 q = 1) : d1856 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1861 q = 1) (hb : d122304 q = 1) : d15379 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1861, d122304, d15379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1861, d122304, d15379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1866 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1867 q = 1) (hb : d122305 q = 1) : d124829 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1867, d122305, d124829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1867, d122305, d124829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22060 (p : Pattern) (ha : d9026 p = 1) (hb : d122306 p = 1) : d124841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1874 q = 1) (hb : d122305 q = 1) : d124831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d124831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22059 q ha hb
    | true =>
      simp only [d1874, d124831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22056 q ha hb
  have h2 (q : Pattern) (ha : d1875 q = 1) (hb : d122305 q = 1) : d124832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d124832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1875, d124832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1876 q = 1) (hb : d122305 q = 1) : d124833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d124833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1876, d124833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9024 q = 1) (hb : d122306 q = 1) : d124834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9024, d122306, d124834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9024, d122306, d124834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1879 q = 1) (hb : d122305 q = 1) : d124836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22056 q ha hb
    | true =>
      simp only [d1879, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22023 q ha hb
  have h7 (q : Pattern) (ha : d1880 q = 1) (hb : d122305 q = 1) : d124837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1881 q = 1) (hb : d122305 q = 1) : d124838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7080 q = 1) (hb : d122306 q = 1) : d124839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7080, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d9025 q = 1) (hb : d122306 q = 1) : d124840 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9025, d124840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9025, d124840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9026 q = 1) (hb : d122306 q = 1) : d124841 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9026, d124841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9026, d124841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro22061 (p : Pattern) (ha : d9032 p = 1) (hb : d122306 p = 1) : d124855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9027 q = 1) (hb : d122306 q = 1) : d124842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9027, d124842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22060 q ha hb
    | true =>
      simp only [d9027, d124842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9028 q = 1) (hb : d122306 q = 1) : d124843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9028, d124843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9028, d124843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7083 q = 1) (hb : d122306 q = 1) : d124850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22058 q ha hb
    | true =>
      simp only [d7083, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7084 q = 1) (hb : d122306 q = 1) : d124851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9029 q = 1) (hb : d122306 q = 1) : d124852 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9029, d124852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9029, d124852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9030 q = 1) (hb : d122306 q = 1) : d124853 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9030, d124853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9030, d124853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9031 q = 1) (hb : d122306 q = 1) : d124854 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9031, d124854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9031, d124854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9032 q = 1) (hb : d122306 q = 1) : d124855 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9032, d124855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9032, d124855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22062 (p : Pattern) (ha : d9036 p = 1) (hb : d122306 p = 1) : d124867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7083 q = 1) (hb : d122306 q = 1) : d124850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22058 q ha hb
    | true =>
      simp only [d7083, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7084 q = 1) (hb : d122306 q = 1) : d124851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7084, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d122306 q = 1) : d124862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22025 q ha hb
    | true =>
      simp only [d1908, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d122306 q = 1) : d124863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9033 q = 1) (hb : d122306 q = 1) : d124864 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9033, d124864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9033, d124864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9034 q = 1) (hb : d122306 q = 1) : d124865 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9034, d124865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9034, d124865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9035 q = 1) (hb : d122306 q = 1) : d124866 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9035, d124866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9035, d124866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9036 q = 1) (hb : d122306 q = 1) : d124867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9036, d124867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9036, d124867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22063 (p : Pattern) (ha : d9050 p = 1) (hb : d122306 p = 1) : d124871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d122305 q = 1) : d124836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22056 q ha hb
    | true =>
      simp only [d1879, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22023 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d122305 q = 1) : d124837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d122305 q = 1) : d124838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7080 q = 1) (hb : d122306 q = 1) : d124839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7080, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1889 q = 1) (hb : d122305 q = 1) : d124856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22023 q ha hb
    | true =>
      simp only [d1889, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22024 q ha hb
  have h7 (q : Pattern) (ha : d1890 q = 1) (hb : d122305 q = 1) : d124857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1891 q = 1) (hb : d122305 q = 1) : d124858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1897 q = 1) (hb : d122306 q = 1) : d124859 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d122306, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1897, d122306, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d9049 q = 1) (hb : d122306 q = 1) : d124870 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9049, d124870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9049, d124870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9050 q = 1) (hb : d122306 q = 1) : d124871 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9050, d124871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9050, d124871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro22064 (p : Pattern) (ha : d9056 p = 1) (hb : d122306 p = 1) : d124877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9051 q = 1) (hb : d122306 q = 1) : d124872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9051, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22063 q ha hb
    | true =>
      simp only [d9051, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d122306 q = 1) : d124873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9053 q = 1) (hb : d122306 q = 1) : d124874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9053, d124874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9053, d124874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9054 q = 1) (hb : d122306 q = 1) : d124875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9054, d124875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9054, d124875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9055 q = 1) (hb : d122306 q = 1) : d124876 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9055, d124876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9055, d124876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9056 q = 1) (hb : d122306 q = 1) : d124877 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9056, d124877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9056, d124877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22065 (p : Pattern) (ha : d94413 p = 1) (hb : d122306 p = 1) : d124883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9037 q = 1) (hb : d122306 q = 1) : d124868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9037, d124868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22061 q ha hb
    | true =>
      simp only [d9037, d124868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22062 q ha hb
  have h2 (q : Pattern) (ha : d94409 q = 1) (hb : d122306 q = 1) : d124869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94409, d124869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94409, d124869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9057 q = 1) (hb : d122306 q = 1) : d124878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9057, d124878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22064 q ha hb
    | true =>
      simp only [d9057, d124878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9058 q = 1) (hb : d122306 q = 1) : d124879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9058, d124879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9058, d124879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94410 q = 1) (hb : d122306 q = 1) : d124880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94410, d124880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94410, d124880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94411 q = 1) (hb : d122306 q = 1) : d124881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94411, d124881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94411, d124881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94412 q = 1) (hb : d122306 q = 1) : d124882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94412, d124882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94412, d124882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94413 q = 1) (hb : d122306 q = 1) : d124883 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94413, d124883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94413, d124883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22066 (p : Pattern) (ha : d94419 p = 1) (hb : d122306 p = 1) : d124900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8924 q = 1) (hb : d122306 q = 1) : d124708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8924, d124708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8924, d124708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22031 q ha hb
  have h2 (q : Pattern) (ha : d8925 q = 1) (hb : d122306 q = 1) : d124709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8925, d124709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8925, d124709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8933 q = 1) (hb : d122306 q = 1) : d124718 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22031 q ha hb
    | true =>
      simp only [d8933, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22033 q ha hb
  have h4 (q : Pattern) (ha : d8934 q = 1) (hb : d122306 q = 1) : d124719 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8934, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8935 q = 1) (hb : d122306 q = 1) : d124720 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8935, d124720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8935, d124720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94397 q = 1) (hb : d122306 q = 1) : d124797 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94397, d124797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22046 q ha hb
    | true =>
      simp only [d94397, d124797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22054 q ha hb
  have h7 (q : Pattern) (ha : d9012 q = 1) (hb : d122306 q = 1) : d124815 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9012, d124815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22037 q ha hb
    | true =>
      simp only [d9012, d124815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22021 q ha hb
  have h8 (q : Pattern) (ha : d94398 q = 1) (hb : d122306 q = 1) : d124816 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94398, d124816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94398, d124816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94399 q = 1) (hb : d122306 q = 1) : d124817 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94399, d124817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94399, d124817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94400 q = 1) (hb : d122306 q = 1) : d124818 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94400, d124818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94400, d124818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94404 q = 1) (hb : d122306 q = 1) : d124822 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94404, d124822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94404, d124822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22055 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d122306 q = 1) : d124824 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d124824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d124824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22022 q ha hb
  have h13 (q : Pattern) (ha : d94405 q = 1) (hb : d122306 q = 1) : d124825 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94405, d124825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94405, d124825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94406 q = 1) (hb : d122306 q = 1) : d124826 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94406, d124826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94406, d124826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94407 q = 1) (hb : d122306 q = 1) : d124827 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94407, d124827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94407, d124827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94408 q = 1) (hb : d122306 q = 1) : d124828 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94408, d124828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94408, d124828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94414 q = 1) (hb : d122306 q = 1) : d124884 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94414, d124884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94414, d124884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22065 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d122306 q = 1) : d124895 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d124895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d124895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22027 q ha hb
  have h19 (q : Pattern) (ha : d94415 q = 1) (hb : d122306 q = 1) : d124896 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94415, d124896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94415, d124896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94416 q = 1) (hb : d122306 q = 1) : d124897 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94416, d124897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94416, d124897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94417 q = 1) (hb : d122306 q = 1) : d124898 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94417, d124898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94417, d124898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94418 q = 1) (hb : d122306 q = 1) : d124899 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94418, d124899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94418, d124899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94419 q = 1) (hb : d122306 q = 1) : d124900 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94419, d124900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94419, d124900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro22067 (p : Pattern) (ha : d94425 p = 1) (hb : d122306 p = 1) : d124906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94420 q = 1) (hb : d122306 q = 1) : d124901 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94420, d124901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94420, d124901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22066 q ha hb
  have h2 (q : Pattern) (ha : d94421 q = 1) (hb : d122306 q = 1) : d124902 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94421, d124902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94421, d124902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94422 q = 1) (hb : d122306 q = 1) : d124903 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94422, d124903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94422, d124903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94423 q = 1) (hb : d122306 q = 1) : d124904 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94423, d124904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94423, d124904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94424 q = 1) (hb : d122306 q = 1) : d124905 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94424, d124905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94424, d124905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94425 q = 1) (hb : d122306 q = 1) : d124906 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94425, d124906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94425, d124906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22068 (p : Pattern) (ha : d2072 p = 1) (hb : d122305 p = 1) : d124912 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2056 q = 1) : d2056 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2068 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2069 q = 1) (hb : d122304 q = 1) : d15547 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2069, d122304, d15547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2069, d122304, d15547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2071 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2072 q = 1) (hb : d122305 q = 1) : d124912 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2072, d122305, d124912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2072, d122305, d124912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22069 (p : Pattern) (ha : d2085 p = 1) (hb : d122305 p = 1) : d13614 p = 1 := by
  have h0 (q : Pattern) (ha : d2071 q = 1) (hb : d122304 q = 1) : d2071 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2084 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2085 q = 1) (hb : d122305 q = 1) : d13614 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2085, d122305, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2085, d122305, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro22070 (p : Pattern) (ha : d2096 p = 1) (hb : d122306 p = 1) : d124926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2086 q = 1) (hb : d122305 q = 1) : d124917 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22068 q ha hb
    | true =>
      simp only [d2086, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22069 q ha hb
  have h2 (q : Pattern) (ha : d2087 q = 1) (hb : d122305 q = 1) : d124918 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2088 q = 1) (hb : d122305 q = 1) : d124919 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2090 q = 1) (hb : d122306 q = 1) : d124920 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d122306, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2090, d122306, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2095 q = 1) (hb : d122306 q = 1) : d124925 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2095, d124925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2095, d124925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2096 q = 1) (hb : d122306 q = 1) : d124926 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2096, d124926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2096, d124926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro22071 (p : Pattern) (ha : d2106 p = 1) (hb : d122306 p = 1) : d124936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d122306 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d122306 q = 1) : d124934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d122306 q = 1) : d124935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2106 q = 1) (hb : d122306 q = 1) : d124936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2106, d124936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2106, d124936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22072 (p : Pattern) (ha : d2116 p = 1) (hb : d122306 p = 1) : d124946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d122306 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d122306 q = 1) : d124934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d122306 q = 1) : d124935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2116 q = 1) (hb : d122306 q = 1) : d124946 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2116, d124946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2116, d124946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22073 (p : Pattern) (ha : d2316 p = 1) (hb : d122306 p = 1) : d125048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2305 q = 1) (hb : d122306 q = 1) : d125037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22071 q ha hb
    | true =>
      simp only [d2305, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2306 q = 1) (hb : d122306 q = 1) : d125038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d122306 q = 1) : d125039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2307, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d122306 q = 1) : d125040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d122306 q = 1) : d125041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2311 q = 1) (hb : d122306 q = 1) : d125043 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22072 q ha hb
    | true =>
      simp only [d2311, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2312 q = 1) (hb : d122306 q = 1) : d125044 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2313 q = 1) (hb : d122306 q = 1) : d125045 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2313, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2314 q = 1) (hb : d122306 q = 1) : d125046 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2315 q = 1) (hb : d122306 q = 1) : d125047 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2316 q = 1) (hb : d122306 q = 1) : d125048 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, d125048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2316, d125048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22074 (p : Pattern) (ha : d2325 p = 1) (hb : d122306 p = 1) : d125057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2311 q = 1) (hb : d122306 q = 1) : d125043 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22072 q ha hb
    | true =>
      simp only [d2311, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2312 q = 1) (hb : d122306 q = 1) : d125044 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2313 q = 1) (hb : d122306 q = 1) : d125045 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2313, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2314 q = 1) (hb : d122306 q = 1) : d125046 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2315 q = 1) (hb : d122306 q = 1) : d125047 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2325 q = 1) (hb : d122306 q = 1) : d125057 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, d125057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, d125057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22075 (p : Pattern) (ha : d2356 p = 1) (hb : d122305 p = 1) : d125068 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2343 q = 1) : d2343 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2349 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2350 q = 1) (hb : d122304 q = 1) : d15785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, d122304, d15785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2350, d122304, d15785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2355 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2356 q = 1) (hb : d122305 q = 1) : d125068 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2356, d122305, d125068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2356, d122305, d125068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22076 (p : Pattern) (ha : d2366 p = 1) (hb : d122305 p = 1) : d13843 p = 1 := by
  have h0 (q : Pattern) (ha : d2355 q = 1) (hb : d122304 q = 1) : d2355 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2365 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2366 q = 1) (hb : d122305 q = 1) : d13843 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2366, d122305, d13843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2366, d122305, d13843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro22077 (p : Pattern) (ha : d2385 p = 1) (hb : d122306 p = 1) : d125094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2367 q = 1) (hb : d122305 q = 1) : d125089 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22075 q ha hb
    | true =>
      simp only [d2367, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22076 q ha hb
  have h2 (q : Pattern) (ha : d2368 q = 1) (hb : d122305 q = 1) : d125090 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2369 q = 1) (hb : d122305 q = 1) : d125091 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2375 q = 1) (hb : d122306 q = 1) : d125092 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d122306, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2375, d122306, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2384 q = 1) (hb : d122306 q = 1) : d125093 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2384, d125093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2384, d125093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2385 q = 1) (hb : d122306 q = 1) : d125094 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2385, d125094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2385, d125094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro22078 (p : Pattern) (ha : d2452 p = 1) (hb : d122306 p = 1) : d125121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2386 q = 1) (hb : d122306 q = 1) : d125095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22077 q ha hb
    | true =>
      simp only [d2386, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2387 q = 1) (hb : d122306 q = 1) : d125096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2449 q = 1) (hb : d122306 q = 1) : d125118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2449, d125118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2449, d125118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2450 q = 1) (hb : d122306 q = 1) : d125119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2450, d125119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2450, d125119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2451 q = 1) (hb : d122306 q = 1) : d125120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2451, d125120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2451, d125120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2452 q = 1) (hb : d122306 q = 1) : d125121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2452, d125121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2452, d125121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22079 (p : Pattern) (ha : d2458 p = 1) (hb : d122306 p = 1) : d125127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2453 q = 1) (hb : d122306 q = 1) : d125122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2453, d125122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22078 q ha hb
    | true =>
      simp only [d2453, d125122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2454 q = 1) (hb : d122306 q = 1) : d125123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, d125123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2454, d125123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2455 q = 1) (hb : d122306 q = 1) : d125124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, d125124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2455, d125124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2456 q = 1) (hb : d122306 q = 1) : d125125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, d125125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, d125125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2457 q = 1) (hb : d122306 q = 1) : d125126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, d125126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, d125126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2458 q = 1) (hb : d122306 q = 1) : d125127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, d125127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, d125127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22080 (p : Pattern) (ha : d2070 p = 1) (hb : d122305 p = 1) : d124911 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2038 q = 1) : d2038 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2056 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2057 q = 1) (hb : d122304 q = 1) : d15544 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2057, d122304, d15544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2057, d122304, d15544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2069 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2070 q = 1) (hb : d122305 q = 1) : d124911 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2070, d122305, d124911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2070, d122305, d124911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22081 (p : Pattern) (ha : d9080 p = 1) (hb : d122306 p = 1) : d124922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2073 q = 1) (hb : d122305 q = 1) : d124913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22080 q ha hb
    | true =>
      simp only [d2073, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22068 q ha hb
  have h2 (q : Pattern) (ha : d2074 q = 1) (hb : d122305 q = 1) : d124914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2075 q = 1) (hb : d122305 q = 1) : d124915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7115 q = 1) (hb : d122306 q = 1) : d124916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7115, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2086 q = 1) (hb : d122305 q = 1) : d124917 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22068 q ha hb
    | true =>
      simp only [d2086, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22069 q ha hb
  have h7 (q : Pattern) (ha : d2087 q = 1) (hb : d122305 q = 1) : d124918 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2088 q = 1) (hb : d122305 q = 1) : d124919 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2090 q = 1) (hb : d122306 q = 1) : d124920 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d122306, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2090, d122306, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d9079 q = 1) (hb : d122306 q = 1) : d124921 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9079, d124921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9079, d124921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9080 q = 1) (hb : d122306 q = 1) : d124922 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9080, d124922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9080, d124922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro22082 (p : Pattern) (ha : d9086 p = 1) (hb : d122306 p = 1) : d124932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22081 q ha hb
    | true =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d122306 q = 1) : d124929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9084 q = 1) (hb : d122306 q = 1) : d124930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9084, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9085 q = 1) (hb : d122306 q = 1) : d124931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9085, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9086 q = 1) (hb : d122306 q = 1) : d124932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9086, d124932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9086, d124932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22083 (p : Pattern) (ha : d9092 p = 1) (hb : d122306 p = 1) : d124942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9087 q = 1) (hb : d122306 q = 1) : d124937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22082 q ha hb
    | true =>
      simp only [d9087, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22071 q ha hb
  have h2 (q : Pattern) (ha : d9088 q = 1) (hb : d122306 q = 1) : d124938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9088, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9089 q = 1) (hb : d122306 q = 1) : d124939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9089, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9090 q = 1) (hb : d122306 q = 1) : d124940 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9090, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9091 q = 1) (hb : d122306 q = 1) : d124941 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9092 q = 1) (hb : d122306 q = 1) : d124942 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9092, d124942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9092, d124942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22084 (p : Pattern) (ha : d9095 p = 1) (hb : d122306 p = 1) : d124945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22081 q ha hb
    | true =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d122306 q = 1) : d124929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9084 q = 1) (hb : d122306 q = 1) : d124930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9084, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9085 q = 1) (hb : d122306 q = 1) : d124931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9085, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9085, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9095 q = 1) (hb : d122306 q = 1) : d124945 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9095, d124945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9095, d124945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22085 (p : Pattern) (ha : d9101 p = 1) (hb : d122306 p = 1) : d124952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9087 q = 1) (hb : d122306 q = 1) : d124937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9087, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22082 q ha hb
    | true =>
      simp only [d9087, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22071 q ha hb
  have h2 (q : Pattern) (ha : d9088 q = 1) (hb : d122306 q = 1) : d124938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9088, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9088, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9089 q = 1) (hb : d122306 q = 1) : d124939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9089, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9089, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9090 q = 1) (hb : d122306 q = 1) : d124940 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9090, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9090, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9091 q = 1) (hb : d122306 q = 1) : d124941 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9091, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9091, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9096 q = 1) (hb : d122306 q = 1) : d124947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22084 q ha hb
    | true =>
      simp only [d9096, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22072 q ha hb
  have h7 (q : Pattern) (ha : d9097 q = 1) (hb : d122306 q = 1) : d124948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9097, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9098 q = 1) (hb : d122306 q = 1) : d124949 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9098, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9099 q = 1) (hb : d122306 q = 1) : d124950 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9100 q = 1) (hb : d122306 q = 1) : d124951 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9101 q = 1) (hb : d122306 q = 1) : d124952 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9101, d124952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9101, d124952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22086 (p : Pattern) (ha : d5237 p = 1) (hb : d122305 p = 1) : d124912 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2056 q = 1) : d2056 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2068 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2069 q = 1) (hb : d122304 q = 1) : d15547 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2069, d122304, d15547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2069, d122304, d15547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5237 q = 1) (hb : d122305 q = 1) : d124912 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5237, d122305, d124912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5237, d122305, d124912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro22087 (p : Pattern) (ha : d7117 p = 1) (hb : d122306 p = 1) : d124986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2073 q = 1) (hb : d122305 q = 1) : d124913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22080 q ha hb
    | true =>
      simp only [d2073, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22068 q ha hb
  have h2 (q : Pattern) (ha : d2074 q = 1) (hb : d122305 q = 1) : d124914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2075 q = 1) (hb : d122305 q = 1) : d124915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7115 q = 1) (hb : d122306 q = 1) : d124916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7115, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5252 q = 1) (hb : d122305 q = 1) : d5252 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5253 q = 1) (hb : d122305 q = 1) : d124981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22086 q ha hb
    | true =>
      simp only [d5253, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5254 q = 1) (hb : d122305 q = 1) : d124982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5255 q = 1) (hb : d122305 q = 1) : d124983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5256 q = 1) (hb : d122306 q = 1) : d124984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5256, d122306, d124984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5256, d122306, d124984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d7116 q = 1) (hb : d122306 q = 1) : d124985 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7116, d124985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7116, d124985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7117 q = 1) (hb : d122306 q = 1) : d124986 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7117, d124986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7117, d124986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro22088 (p : Pattern) (ha : d9129 p = 1) (hb : d122306 p = 1) : d124996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7118 q = 1) (hb : d122306 q = 1) : d124987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22087 q ha hb
    | true =>
      simp only [d7118, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7119 q = 1) (hb : d122306 q = 1) : d124988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9126 q = 1) (hb : d122306 q = 1) : d124993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9126, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9127 q = 1) (hb : d122306 q = 1) : d124994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9127, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9128 q = 1) (hb : d122306 q = 1) : d124995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9128, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9129 q = 1) (hb : d122306 q = 1) : d124996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9129, d124996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9129, d124996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22089 (p : Pattern) (ha : d9180 p = 1) (hb : d122306 p = 1) : d125042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9175 q = 1) (hb : d122306 q = 1) : d125032 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9175, d125032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22088 q ha hb
    | true =>
      simp only [d9175, d125032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22071 q ha hb
  have h2 (q : Pattern) (ha : d9176 q = 1) (hb : d122306 q = 1) : d125033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9176, d125033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9176, d125033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9177 q = 1) (hb : d122306 q = 1) : d125034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9177, d125034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9177, d125034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9178 q = 1) (hb : d122306 q = 1) : d125035 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9178, d125035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9178, d125035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9179 q = 1) (hb : d122306 q = 1) : d125036 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9179, d125036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9179, d125036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d122306 q = 1) : d125037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22071 q ha hb
    | true =>
      simp only [d2305, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d122306 q = 1) : d125038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d122306 q = 1) : d125039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d122306 q = 1) : d125040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d122306 q = 1) : d125041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9180 q = 1) (hb : d122306 q = 1) : d125042 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9180, d125042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9180, d125042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22090 (p : Pattern) (ha : d2129 p = 1) (hb : d122306 p = 1) : d124959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d122306 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d122306 q = 1) : d124934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d122306 q = 1) : d124958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2129 q = 1) (hb : d122306 q = 1) : d124959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2129, d124959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2129, d124959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22091 (p : Pattern) (ha : d2139 p = 1) (hb : d122306 p = 1) : d124969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d122306 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d122306 q = 1) : d124967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d122306 q = 1) : d124968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d122306 q = 1) : d124969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2139, d124969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2139, d124969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22092 (p : Pattern) (ha : d9106 p = 1) (hb : d122306 p = 1) : d124957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22081 q ha hb
    | true =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d122306 q = 1) : d124929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9084 q = 1) (hb : d122306 q = 1) : d124930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9084, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9105 q = 1) (hb : d122306 q = 1) : d124956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9105, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9106 q = 1) (hb : d122306 q = 1) : d124957 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9106, d124957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9106, d124957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22093 (p : Pattern) (ha : d9113 p = 1) (hb : d122306 p = 1) : d124966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22081 q ha hb
    | true =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d122306 q = 1) : d124929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9111 q = 1) (hb : d122306 q = 1) : d124964 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9111, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9112 q = 1) (hb : d122306 q = 1) : d124965 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9112, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9113 q = 1) (hb : d122306 q = 1) : d124966 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9113, d124966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9113, d124966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22094 (p : Pattern) (ha : d2149 p = 1) (hb : d122305 p = 1) : d15621 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2147 q = 1) : d2147 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2148 q = 1) (hb : d122304 q = 1) : d15620 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2148, d122304, d15620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2148, d122304, d15620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2057 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2149 q = 1) (hb : d122305 q = 1) : d15621 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2149, d122305, d15621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2149, d122305, d15621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22095 (p : Pattern) (ha : d9119 p = 1) (hb : d122306 p = 1) : d124978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2150 q = 1) (hb : d122305 q = 1) : d124973 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2150, d124973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22094 q ha hb
    | true =>
      simp only [d2150, d124973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22080 q ha hb
  have h2 (q : Pattern) (ha : d2151 q = 1) (hb : d122305 q = 1) : d124974 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2151, d124974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2151, d124974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2152 q = 1) (hb : d122305 q = 1) : d124975 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2152, d124975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2152, d124975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9117 q = 1) (hb : d122306 q = 1) : d124976 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9117, d122306, d124976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9117, d122306, d124976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2073 q = 1) (hb : d122305 q = 1) : d124913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22080 q ha hb
    | true =>
      simp only [d2073, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22068 q ha hb
  have h7 (q : Pattern) (ha : d2074 q = 1) (hb : d122305 q = 1) : d124914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2075 q = 1) (hb : d122305 q = 1) : d124915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7115 q = 1) (hb : d122306 q = 1) : d124916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7115, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d9118 q = 1) (hb : d122306 q = 1) : d124977 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9118, d124977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9118, d124977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9119 q = 1) (hb : d122306 q = 1) : d124978 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9119, d124978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9119, d124978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro22096 (p : Pattern) (ha : d9125 p = 1) (hb : d122306 p = 1) : d124992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9120 q = 1) (hb : d122306 q = 1) : d124979 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22095 q ha hb
    | true =>
      simp only [d9120, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9121 q = 1) (hb : d122306 q = 1) : d124980 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9121, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7118 q = 1) (hb : d122306 q = 1) : d124987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22087 q ha hb
    | true =>
      simp only [d7118, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7119 q = 1) (hb : d122306 q = 1) : d124988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9122 q = 1) (hb : d122306 q = 1) : d124989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9122, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9123 q = 1) (hb : d122306 q = 1) : d124990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9123, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9124 q = 1) (hb : d122306 q = 1) : d124991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9124, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9125 q = 1) (hb : d122306 q = 1) : d124992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9125, d124992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9125, d124992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22097 (p : Pattern) (ha : d9145 p = 1) (hb : d122306 p = 1) : d125002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22081 q ha hb
    | true =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d122306 q = 1) : d124999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9143 q = 1) (hb : d122306 q = 1) : d125000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9143, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9144 q = 1) (hb : d122306 q = 1) : d125001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9144, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9145 q = 1) (hb : d122306 q = 1) : d125002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9145, d125002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9145, d125002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22098 (p : Pattern) (ha : d94434 p = 1) (hb : d122306 p = 1) : d125008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9107 q = 1) (hb : d122306 q = 1) : d124960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22092 q ha hb
    | true =>
      simp only [d9107, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22090 q ha hb
  have h2 (q : Pattern) (ha : d9108 q = 1) (hb : d122306 q = 1) : d124961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9108, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9109 q = 1) (hb : d122306 q = 1) : d124962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9109, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9110 q = 1) (hb : d122306 q = 1) : d124963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9110, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9114 q = 1) (hb : d122306 q = 1) : d124970 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22093 q ha hb
    | true =>
      simp only [d9114, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22091 q ha hb
  have h6 (q : Pattern) (ha : d9115 q = 1) (hb : d122306 q = 1) : d124971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9115, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9116 q = 1) (hb : d122306 q = 1) : d124972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9116, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9130 q = 1) (hb : d122306 q = 1) : d124997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22096 q ha hb
    | true =>
      simp only [d9130, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22088 q ha hb
  have h9 (q : Pattern) (ha : d94430 q = 1) (hb : d122306 q = 1) : d124998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94430, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9146 q = 1) (hb : d122306 q = 1) : d125003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22097 q ha hb
    | true =>
      simp only [d9146, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9147 q = 1) (hb : d122306 q = 1) : d125004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9147, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94431 q = 1) (hb : d122306 q = 1) : d125005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94431, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94432 q = 1) (hb : d122306 q = 1) : d125006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94432, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94433 q = 1) (hb : d122306 q = 1) : d125007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94433, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94434 q = 1) (hb : d122306 q = 1) : d125008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94434, d125008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94434, d125008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro22099 (p : Pattern) (ha : d2282 p = 1) (hb : d122306 p = 1) : d125010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d122306 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d122306 q = 1) : d124934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d122306 q = 1) : d124958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2282 q = 1) (hb : d122306 q = 1) : d125010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2282, d125010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2282, d125010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22100 (p : Pattern) (ha : d2288 p = 1) (hb : d122306 p = 1) : d125016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d122306 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d122306 q = 1) : d124967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d122306 q = 1) : d124968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2288 q = 1) (hb : d122306 q = 1) : d125016 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2288, d125016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2288, d125016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22101 (p : Pattern) (ha : d9152 p = 1) (hb : d122306 p = 1) : d125009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22081 q ha hb
    | true =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d122306 q = 1) : d124929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9084 q = 1) (hb : d122306 q = 1) : d124930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9084, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9084, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9105 q = 1) (hb : d122306 q = 1) : d124956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9105, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9105, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9152 q = 1) (hb : d122306 q = 1) : d125009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9152, d125009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9152, d125009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22102 (p : Pattern) (ha : d9157 p = 1) (hb : d122306 p = 1) : d125015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22081 q ha hb
    | true =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9083 q = 1) (hb : d122306 q = 1) : d124929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9083, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9083, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9111 q = 1) (hb : d122306 q = 1) : d124964 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9111, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9111, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9112 q = 1) (hb : d122306 q = 1) : d124965 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9112, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9112, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9157 q = 1) (hb : d122306 q = 1) : d125015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9157, d125015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9157, d125015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22103 (p : Pattern) (ha : d9161 p = 1) (hb : d122306 p = 1) : d125020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9120 q = 1) (hb : d122306 q = 1) : d124979 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9120, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22095 q ha hb
    | true =>
      simp only [d9120, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9121 q = 1) (hb : d122306 q = 1) : d124980 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9121, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9121, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7118 q = 1) (hb : d122306 q = 1) : d124987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22087 q ha hb
    | true =>
      simp only [d7118, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7119 q = 1) (hb : d122306 q = 1) : d124988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9122 q = 1) (hb : d122306 q = 1) : d124989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9122, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9122, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9123 q = 1) (hb : d122306 q = 1) : d124990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9123, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9123, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9124 q = 1) (hb : d122306 q = 1) : d124991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9124, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9124, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9161 q = 1) (hb : d122306 q = 1) : d125020 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9161, d125020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9161, d125020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22104 (p : Pattern) (ha : d9162 p = 1) (hb : d122306 p = 1) : d125021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7118 q = 1) (hb : d122306 q = 1) : d124987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22087 q ha hb
    | true =>
      simp only [d7118, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7119 q = 1) (hb : d122306 q = 1) : d124988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7119, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22070 q ha hb
    | true =>
      simp only [d2097, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9126 q = 1) (hb : d122306 q = 1) : d124993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9126, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9126, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9127 q = 1) (hb : d122306 q = 1) : d124994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9127, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9127, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9128 q = 1) (hb : d122306 q = 1) : d124995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9128, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9128, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9162 q = 1) (hb : d122306 q = 1) : d125021 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9162, d125021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9162, d125021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22105 (p : Pattern) (ha : d9167 p = 1) (hb : d122306 p = 1) : d125024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9081 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22081 q ha hb
    | true =>
      simp only [d9081, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9082 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9082, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9142 q = 1) (hb : d122306 q = 1) : d124999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9142, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9142, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9143 q = 1) (hb : d122306 q = 1) : d125000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9143, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9143, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9144 q = 1) (hb : d122306 q = 1) : d125001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9144, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9144, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9167 q = 1) (hb : d122306 q = 1) : d125024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9167, d125024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9167, d125024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22106 (p : Pattern) (ha : d94439 p = 1) (hb : d122306 p = 1) : d125030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9107 q = 1) (hb : d122306 q = 1) : d124960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9107, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22092 q ha hb
    | true =>
      simp only [d9107, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22090 q ha hb
  have h2 (q : Pattern) (ha : d9108 q = 1) (hb : d122306 q = 1) : d124961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9108, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9108, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9109 q = 1) (hb : d122306 q = 1) : d124962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9109, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9109, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9110 q = 1) (hb : d122306 q = 1) : d124963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9110, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9110, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9114 q = 1) (hb : d122306 q = 1) : d124970 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9114, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22093 q ha hb
    | true =>
      simp only [d9114, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22091 q ha hb
  have h6 (q : Pattern) (ha : d9115 q = 1) (hb : d122306 q = 1) : d124971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9115, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9115, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9116 q = 1) (hb : d122306 q = 1) : d124972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9116, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9116, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9130 q = 1) (hb : d122306 q = 1) : d124997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9130, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22096 q ha hb
    | true =>
      simp only [d9130, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22088 q ha hb
  have h9 (q : Pattern) (ha : d94430 q = 1) (hb : d122306 q = 1) : d124998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94430, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9146 q = 1) (hb : d122306 q = 1) : d125003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9146, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22097 q ha hb
    | true =>
      simp only [d9146, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9147 q = 1) (hb : d122306 q = 1) : d125004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9147, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9147, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94431 q = 1) (hb : d122306 q = 1) : d125005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94431, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94432 q = 1) (hb : d122306 q = 1) : d125006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94432, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94433 q = 1) (hb : d122306 q = 1) : d125007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94433, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9153 q = 1) (hb : d122306 q = 1) : d125011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9153, d125011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22101 q ha hb
    | true =>
      simp only [d9153, d125011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22099 q ha hb
  have h16 (q : Pattern) (ha : d9154 q = 1) (hb : d122306 q = 1) : d125012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9154, d125012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9154, d125012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9155 q = 1) (hb : d122306 q = 1) : d125013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9155, d125013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9155, d125013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9156 q = 1) (hb : d122306 q = 1) : d125014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9156, d125014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9156, d125014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9158 q = 1) (hb : d122306 q = 1) : d125017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9158, d125017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22102 q ha hb
    | true =>
      simp only [d9158, d125017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22100 q ha hb
  have h20 (q : Pattern) (ha : d9159 q = 1) (hb : d122306 q = 1) : d125018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9159, d125018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9159, d125018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9160 q = 1) (hb : d122306 q = 1) : d125019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9160, d125019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9160, d125019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9163 q = 1) (hb : d122306 q = 1) : d125022 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22103 q ha hb
    | true =>
      simp only [d9163, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22104 q ha hb
  have h23 (q : Pattern) (ha : d94435 q = 1) (hb : d122306 q = 1) : d125023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94435, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d9168 q = 1) (hb : d122306 q = 1) : d125025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22105 q ha hb
    | true =>
      simp only [d9168, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9169 q = 1) (hb : d122306 q = 1) : d125026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9169, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94436 q = 1) (hb : d122306 q = 1) : d125027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94436, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94437 q = 1) (hb : d122306 q = 1) : d125028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94437, d125028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94437, d125028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94438 q = 1) (hb : d122306 q = 1) : d125029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94438, d125029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94438, d125029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94439 q = 1) (hb : d122306 q = 1) : d125030 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94439, d125030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94439, d125030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro22107 (p : Pattern) (ha : d94446 p = 1) (hb : d122306 p = 1) : d125055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9163 q = 1) (hb : d122306 q = 1) : d125022 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9163, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22103 q ha hb
    | true =>
      simp only [d9163, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22104 q ha hb
  have h2 (q : Pattern) (ha : d94435 q = 1) (hb : d122306 q = 1) : d125023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94435, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9168 q = 1) (hb : d122306 q = 1) : d125025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9168, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22105 q ha hb
    | true =>
      simp only [d9168, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9169 q = 1) (hb : d122306 q = 1) : d125026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9169, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9169, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94436 q = 1) (hb : d122306 q = 1) : d125027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94436, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94444 q = 1) (hb : d122306 q = 1) : d125053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94444, d125053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94444, d125053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94445 q = 1) (hb : d122306 q = 1) : d125054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94445, d125054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94445, d125054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94446 q = 1) (hb : d122306 q = 1) : d125055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94446, d125055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94446, d125055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22108 (p : Pattern) (ha : d2351 p = 1) (hb : d122305 p = 1) : d125063 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2338 q = 1) : d2338 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2343 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2344 q = 1) (hb : d122304 q = 1) : d15769 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2344, d122304, d15769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2344, d122304, d15769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2350 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2351 q = 1) (hb : d122305 q = 1) : d125063 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2351, d122305, d125063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2351, d122305, d125063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22109 (p : Pattern) (ha : d6642 p = 1) (hb : d122305 p = 1) : d125068 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2343 q = 1) : d2343 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2349 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2350 q = 1) (hb : d122304 q = 1) : d15785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, d122304, d15785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2350, d122304, d15785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6642 q = 1) (hb : d122305 q = 1) : d125068 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6642, d122305, d125068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6642, d122305, d125068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro22110 (p : Pattern) (ha : d7163 p = 1) (hb : d122306 p = 1) : d125082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2357 q = 1) (hb : d122305 q = 1) : d125069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22108 q ha hb
    | true =>
      simp only [d2357, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22075 q ha hb
  have h2 (q : Pattern) (ha : d2358 q = 1) (hb : d122305 q = 1) : d125070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2359 q = 1) (hb : d122305 q = 1) : d125071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7161 q = 1) (hb : d122306 q = 1) : d125072 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7161, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6648 q = 1) (hb : d122305 q = 1) : d6648 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6649 q = 1) (hb : d122305 q = 1) : d125077 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22109 q ha hb
    | true =>
      simp only [d6649, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6650 q = 1) (hb : d122305 q = 1) : d125078 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6651 q = 1) (hb : d122305 q = 1) : d125079 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6652 q = 1) (hb : d122306 q = 1) : d125080 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, d122306, d125080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6652, d122306, d125080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d7162 q = 1) (hb : d122306 q = 1) : d125081 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7162, d125081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7162, d125081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7163 q = 1) (hb : d122306 q = 1) : d125082 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7163, d125082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7163, d125082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro22111 (p : Pattern) (ha : d2345 p = 1) (hb : d122305 p = 1) : d15768 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2334 q = 1) : d2334 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2339 q = 1) (hb : d122304 q = 1) : d15767 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2339, d122304, d15767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2339, d122304, d15767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2344 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2345 q = 1) (hb : d122305 q = 1) : d15768 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d2345, d122305, d15768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2345, d122305, d15768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro22112 (p : Pattern) (ha : d9195 p = 1) (hb : d122306 p = 1) : d125074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2352 q = 1) (hb : d122305 q = 1) : d125064 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, d125064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22111 q ha hb
    | true =>
      simp only [d2352, d125064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22108 q ha hb
  have h2 (q : Pattern) (ha : d2353 q = 1) (hb : d122305 q = 1) : d125065 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, d125065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2353, d125065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2354 q = 1) (hb : d122305 q = 1) : d125066 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, d125066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2354, d125066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9193 q = 1) (hb : d122306 q = 1) : d125067 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9193, d122306, d125067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9193, d122306, d125067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2357 q = 1) (hb : d122305 q = 1) : d125069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22108 q ha hb
    | true =>
      simp only [d2357, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22075 q ha hb
  have h7 (q : Pattern) (ha : d2358 q = 1) (hb : d122305 q = 1) : d125070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2359 q = 1) (hb : d122305 q = 1) : d125071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7161 q = 1) (hb : d122306 q = 1) : d125072 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7161, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d9194 q = 1) (hb : d122306 q = 1) : d125073 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9194, d125073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9194, d125073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9195 q = 1) (hb : d122306 q = 1) : d125074 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9195, d125074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9195, d125074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro22113 (p : Pattern) (ha : d9201 p = 1) (hb : d122306 p = 1) : d125088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9196 q = 1) (hb : d122306 q = 1) : d125075 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9196, d125075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22112 q ha hb
    | true =>
      simp only [d9196, d125075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9197 q = 1) (hb : d122306 q = 1) : d125076 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9197, d125076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9197, d125076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7164 q = 1) (hb : d122306 q = 1) : d125083 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22110 q ha hb
    | true =>
      simp only [d7164, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7165 q = 1) (hb : d122306 q = 1) : d125084 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9198 q = 1) (hb : d122306 q = 1) : d125085 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9198, d125085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9198, d125085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9199 q = 1) (hb : d122306 q = 1) : d125086 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9199, d125086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9199, d125086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9200 q = 1) (hb : d122306 q = 1) : d125087 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9200, d125087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9200, d125087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9201 q = 1) (hb : d122306 q = 1) : d125088 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9201, d125088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9201, d125088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22114 (p : Pattern) (ha : d9205 p = 1) (hb : d122306 p = 1) : d125100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7164 q = 1) (hb : d122306 q = 1) : d125083 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22110 q ha hb
    | true =>
      simp only [d7164, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7165 q = 1) (hb : d122306 q = 1) : d125084 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d122306 q = 1) : d125095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22077 q ha hb
    | true =>
      simp only [d2386, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d122306 q = 1) : d125096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9202 q = 1) (hb : d122306 q = 1) : d125097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9202, d125097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9202, d125097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9203 q = 1) (hb : d122306 q = 1) : d125098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9203, d125098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9203, d125098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9204 q = 1) (hb : d122306 q = 1) : d125099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9204, d125099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9204, d125099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9205 q = 1) (hb : d122306 q = 1) : d125100 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9205, d125100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9205, d125100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22115 (p : Pattern) (ha : d9219 p = 1) (hb : d122306 p = 1) : d125104 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2357 q = 1) (hb : d122305 q = 1) : d125069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22108 q ha hb
    | true =>
      simp only [d2357, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22075 q ha hb
  have h2 (q : Pattern) (ha : d2358 q = 1) (hb : d122305 q = 1) : d125070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2359 q = 1) (hb : d122305 q = 1) : d125071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7161 q = 1) (hb : d122306 q = 1) : d125072 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7161, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2367 q = 1) (hb : d122305 q = 1) : d125089 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22075 q ha hb
    | true =>
      simp only [d2367, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22076 q ha hb
  have h7 (q : Pattern) (ha : d2368 q = 1) (hb : d122305 q = 1) : d125090 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2369 q = 1) (hb : d122305 q = 1) : d125091 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2375 q = 1) (hb : d122306 q = 1) : d125092 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d122306, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2375, d122306, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d9218 q = 1) (hb : d122306 q = 1) : d125103 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9218, d125103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9218, d125103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9219 q = 1) (hb : d122306 q = 1) : d125104 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9219, d125104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9219, d125104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro22116 (p : Pattern) (ha : d9225 p = 1) (hb : d122306 p = 1) : d125110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9220 q = 1) (hb : d122306 q = 1) : d125105 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9220, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22115 q ha hb
    | true =>
      simp only [d9220, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9221 q = 1) (hb : d122306 q = 1) : d125106 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9221, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9222 q = 1) (hb : d122306 q = 1) : d125107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9222, d125107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9222, d125107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9223 q = 1) (hb : d122306 q = 1) : d125108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9223, d125108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9223, d125108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9224 q = 1) (hb : d122306 q = 1) : d125109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9224, d125109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9224, d125109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9225 q = 1) (hb : d122306 q = 1) : d125110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9225, d125110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9225, d125110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22117 (p : Pattern) (ha : d94456 p = 1) (hb : d122306 p = 1) : d125116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9206 q = 1) (hb : d122306 q = 1) : d125101 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9206, d125101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22113 q ha hb
    | true =>
      simp only [d9206, d125101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22114 q ha hb
  have h2 (q : Pattern) (ha : d94452 q = 1) (hb : d122306 q = 1) : d125102 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94452, d125102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94452, d125102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9226 q = 1) (hb : d122306 q = 1) : d125111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9226, d125111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22116 q ha hb
    | true =>
      simp only [d9226, d125111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9227 q = 1) (hb : d122306 q = 1) : d125112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9227, d125112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9227, d125112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94453 q = 1) (hb : d122306 q = 1) : d125113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94453, d125113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94453, d125113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94454 q = 1) (hb : d122306 q = 1) : d125114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94454, d125114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94454, d125114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94455 q = 1) (hb : d122306 q = 1) : d125115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94455, d125115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94455, d125115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94456 q = 1) (hb : d122306 q = 1) : d125116 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94456, d125116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94456, d125116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22118 (p : Pattern) (ha : d94462 p = 1) (hb : d122306 p = 1) : d125133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9093 q = 1) (hb : d122306 q = 1) : d124943 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9093, d124943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9093, d124943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22083 q ha hb
  have h2 (q : Pattern) (ha : d9094 q = 1) (hb : d122306 q = 1) : d124944 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9094, d124944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9094, d124944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9102 q = 1) (hb : d122306 q = 1) : d124953 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22083 q ha hb
    | true =>
      simp only [d9102, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22085 q ha hb
  have h4 (q : Pattern) (ha : d9103 q = 1) (hb : d122306 q = 1) : d124954 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9103, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9104 q = 1) (hb : d122306 q = 1) : d124955 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9104, d124955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9104, d124955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94440 q = 1) (hb : d122306 q = 1) : d125031 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94440, d125031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22098 q ha hb
    | true =>
      simp only [d94440, d125031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22106 q ha hb
  have h7 (q : Pattern) (ha : d9181 q = 1) (hb : d122306 q = 1) : d125049 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9181, d125049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22089 q ha hb
    | true =>
      simp only [d9181, d125049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22073 q ha hb
  have h8 (q : Pattern) (ha : d94441 q = 1) (hb : d122306 q = 1) : d125050 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94441, d125050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94441, d125050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94442 q = 1) (hb : d122306 q = 1) : d125051 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94442, d125051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94442, d125051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94443 q = 1) (hb : d122306 q = 1) : d125052 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94443, d125052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94443, d125052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94447 q = 1) (hb : d122306 q = 1) : d125056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94447, d125056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94447, d125056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22107 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d122306 q = 1) : d125058 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d125058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d125058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22074 q ha hb
  have h13 (q : Pattern) (ha : d94448 q = 1) (hb : d122306 q = 1) : d125059 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94448, d125059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94448, d125059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94449 q = 1) (hb : d122306 q = 1) : d125060 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94449, d125060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94449, d125060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94450 q = 1) (hb : d122306 q = 1) : d125061 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94450, d125061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94450, d125061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94451 q = 1) (hb : d122306 q = 1) : d125062 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94451, d125062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94451, d125062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94457 q = 1) (hb : d122306 q = 1) : d125117 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94457, d125117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94457, d125117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22117 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d122306 q = 1) : d125128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d125128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, d125128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22079 q ha hb
  have h19 (q : Pattern) (ha : d94458 q = 1) (hb : d122306 q = 1) : d125129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94458, d125129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94458, d125129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94459 q = 1) (hb : d122306 q = 1) : d125130 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94459, d125130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94459, d125130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94460 q = 1) (hb : d122306 q = 1) : d125131 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94460, d125131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94460, d125131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94461 q = 1) (hb : d122306 q = 1) : d125132 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94461, d125132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94461, d125132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94462 q = 1) (hb : d122306 q = 1) : d125133 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94462, d125133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94462, d125133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro22119 (p : Pattern) (ha : d94468 p = 1) (hb : d122306 p = 1) : d125139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94463 q = 1) (hb : d122306 q = 1) : d125134 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94463, d125134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94463, d125134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22118 q ha hb
  have h2 (q : Pattern) (ha : d94464 q = 1) (hb : d122306 q = 1) : d125135 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94464, d125135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94464, d125135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94465 q = 1) (hb : d122306 q = 1) : d125136 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94465, d125136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94465, d125136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94466 q = 1) (hb : d122306 q = 1) : d125137 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94466, d125137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94466, d125137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94467 q = 1) (hb : d122306 q = 1) : d125138 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94467, d125138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94467, d125138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94468 q = 1) (hb : d122306 q = 1) : d125139 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94468, d125139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94468, d125139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22120 (p : Pattern) (ha : d94474 p = 1) (hb : d122306 p = 1) : d125145 p = 1 := by
  have h0 (q : Pattern) (ha : d94303 q = 1) (hb : d122306 q = 1) : d124246 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94303, d124246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21869 q ha hb
    | true =>
      simp only [d94303, d124246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21913 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94343 q = 1) (hb : d122306 q = 1) : d124440 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94343, d124440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94343, d124440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21963 q ha hb
  have h3 (q : Pattern) (ha : d94344 q = 1) (hb : d122306 q = 1) : d124441 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94344, d124441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94344, d124441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94384 q = 1) (hb : d122306 q = 1) : d124673 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94384, d124673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94384, d124673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22015 q ha hb
  have h5 (q : Pattern) (ha : d94385 q = 1) (hb : d122306 q = 1) : d124674 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94385, d124674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94385, d124674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94386 q = 1) (hb : d122306 q = 1) : d124675 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94386, d124675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94386, d124675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94426 q = 1) (hb : d122306 q = 1) : d124907 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94426, d124907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94426, d124907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22067 q ha hb
  have h8 (q : Pattern) (ha : d94427 q = 1) (hb : d122306 q = 1) : d124908 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94427, d124908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94427, d124908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94428 q = 1) (hb : d122306 q = 1) : d124909 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94428, d124909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94428, d124909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94429 q = 1) (hb : d122306 q = 1) : d124910 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94429, d124910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94429, d124910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94469 q = 1) (hb : d122306 q = 1) : d125140 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94469, d125140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94469, d125140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22119 q ha hb
  have h12 (q : Pattern) (ha : d94470 q = 1) (hb : d122306 q = 1) : d125141 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94470, d125141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94470, d125141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94471 q = 1) (hb : d122306 q = 1) : d125142 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94471, d125142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94471, d125142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94472 q = 1) (hb : d122306 q = 1) : d125143 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94472, d125143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94472, d125143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94473 q = 1) (hb : d122306 q = 1) : d125144 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94473, d125144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94473, d125144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94474 q = 1) (hb : d122306 q = 1) : d125145 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94474, d125145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94474, d125145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro22121 (p : Pattern) (ha : d94480 p = 1) (hb : d122306 p = 1) : d125151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94475 q = 1) (hb : d122306 q = 1) : d125146 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94475, d125146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22120 q ha hb
    | true =>
      simp only [d94475, d125146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94476 q = 1) (hb : d122306 q = 1) : d125147 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94476, d125147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94476, d125147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94477 q = 1) (hb : d122306 q = 1) : d125148 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94477, d125148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94477, d125148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94478 q = 1) (hb : d122306 q = 1) : d125149 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94478, d125149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94478, d125149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94479 q = 1) (hb : d122306 q = 1) : d125150 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94479, d125150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94479, d125150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94480 q = 1) (hb : d122306 q = 1) : d125151 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94480, d125151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94480, d125151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22122 (p : Pattern) (ha : d94486 p = 1) (hb : d122306 p = 1) : d125157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94481 q = 1) (hb : d122306 q = 1) : d125152 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94481, d125152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22121 q ha hb
    | true =>
      simp only [d94481, d125152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94482 q = 1) (hb : d122306 q = 1) : d125153 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94482, d125153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94482, d125153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94483 q = 1) (hb : d122306 q = 1) : d125154 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94483, d125154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94483, d125154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94484 q = 1) (hb : d122306 q = 1) : d125155 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94484, d125155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94484, d125155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94485 q = 1) (hb : d122306 q = 1) : d125156 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94485, d125156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94485, d125156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94486 q = 1) (hb : d122306 q = 1) : d125157 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94486, d125157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94486, d125157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22123 (p : Pattern) (ha : d94492 p = 1) (hb : d122306 p = 1) : d125163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94487 q = 1) (hb : d122306 q = 1) : d125158 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94487, d125158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22122 q ha hb
    | true =>
      simp only [d94487, d125158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94488 q = 1) (hb : d122306 q = 1) : d125159 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94488, d125159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94488, d125159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94489 q = 1) (hb : d122306 q = 1) : d125160 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94489, d125160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94489, d125160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94490 q = 1) (hb : d122306 q = 1) : d125161 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94490, d125161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94490, d125161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94491 q = 1) (hb : d122306 q = 1) : d125162 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94491, d125162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94491, d125162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94492 q = 1) (hb : d122306 q = 1) : d125163 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94492, d125163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94492, d125163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22124 (p : Pattern) (ha : d94498 p = 1) (hb : d122306 p = 1) : d125169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94493 q = 1) (hb : d122306 q = 1) : d125164 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94493, d125164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22123 q ha hb
    | true =>
      simp only [d94493, d125164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94494 q = 1) (hb : d122306 q = 1) : d125165 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94494, d125165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94494, d125165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94495 q = 1) (hb : d122306 q = 1) : d125166 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94495, d125166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94495, d125166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94496 q = 1) (hb : d122306 q = 1) : d125167 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94496, d125167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94496, d125167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94497 q = 1) (hb : d122306 q = 1) : d125168 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94497, d125168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94497, d125168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94498 q = 1) (hb : d122306 q = 1) : d125169 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94498, d125169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94498, d125169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22125 (p : Pattern) (ha : d94504 p = 1) (hb : d122306 p = 1) : d125175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94499 q = 1) (hb : d122306 q = 1) : d125170 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94499, d125170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22124 q ha hb
    | true =>
      simp only [d94499, d125170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94500 q = 1) (hb : d122306 q = 1) : d125171 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94500, d125171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94500, d125171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94501 q = 1) (hb : d122306 q = 1) : d125172 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94501, d125172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94501, d125172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94502 q = 1) (hb : d122306 q = 1) : d125173 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94502, d125173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94502, d125173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94503 q = 1) (hb : d122306 q = 1) : d125174 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94503, d125174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94503, d125174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94504 q = 1) (hb : d122306 q = 1) : d125175 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94504, d125175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94504, d125175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22126 (p : Pattern) (ha : d94510 p = 1) (hb : d122306 p = 1) : d125181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94505 q = 1) (hb : d122306 q = 1) : d125176 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94505, d125176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22125 q ha hb
    | true =>
      simp only [d94505, d125176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94506 q = 1) (hb : d122306 q = 1) : d125177 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94506, d125177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94506, d125177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94507 q = 1) (hb : d122306 q = 1) : d125178 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94507, d125178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94507, d125178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94508 q = 1) (hb : d122306 q = 1) : d125179 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94508, d125179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94508, d125179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94509 q = 1) (hb : d122306 q = 1) : d125180 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94509, d125180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94509, d125180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94510 q = 1) (hb : d122306 q = 1) : d125181 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94510, d125181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94510, d125181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22127 (p : Pattern) (ha : d94516 p = 1) (hb : d122306 p = 1) : d125187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94511 q = 1) (hb : d122306 q = 1) : d125182 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94511, d125182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22126 q ha hb
    | true =>
      simp only [d94511, d125182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94512 q = 1) (hb : d122306 q = 1) : d125183 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94512, d125183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94512, d125183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94513 q = 1) (hb : d122306 q = 1) : d125184 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94513, d125184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94513, d125184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94514 q = 1) (hb : d122306 q = 1) : d125185 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94514, d125185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94514, d125185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94515 q = 1) (hb : d122306 q = 1) : d125186 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94515, d125186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94515, d125186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94516 q = 1) (hb : d122306 q = 1) : d125187 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94516, d125187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94516, d125187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22128 (p : Pattern) (ha : d122308 p = 1) (hb : d123879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13980 q = 1) (hb : d122307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13980, d122307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13980, d122307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122308 q = 1) (hb : d123879 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122308, d123879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d122308, d123879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro22129 (p : Pattern) (ha : d122314 p = 1) (hb : d123885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122309 q = 1) (hb : d123880 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122309, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22128 q ha hb
    | true =>
      simp only [d122309, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h2 (q : Pattern) (ha : d122310 q = 1) (hb : d123881 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122310, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122310, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122311 q = 1) (hb : d123882 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122311, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122311, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122312 q = 1) (hb : d123883 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122312, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122312, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d122313 q = 1) (hb : d123884 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122313, d123884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122313, d123884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122314 q = 1) (hb : d123885 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122314, d123885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122314, d123885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22130 (p : Pattern) (ha : d122320 p = 1) (hb : d123891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22129 q ha hb
    | true =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122317 q = 1) (hb : d123888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122317, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122317, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122318 q = 1) (hb : d123889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122318, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122318, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122319 q = 1) (hb : d123890 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122319, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122319, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122320 q = 1) (hb : d123891 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122320, d123891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122320, d123891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22131 (p : Pattern) (ha : d122326 p = 1) (hb : d123897 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d122321 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22130 q ha hb
    | true =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122322 q = 1) (hb : d123893 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122322, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122322, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d122323 q = 1) (hb : d123894 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122323, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122323, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122324 q = 1) (hb : d123895 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122324, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122324, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122325 q = 1) (hb : d123896 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122325, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122325, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122326 q = 1) (hb : d123897 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122326, d123897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122326, d123897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22132 (p : Pattern) (ha : d122327 p = 1) (hb : d123898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22129 q ha hb
    | true =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122317 q = 1) (hb : d123888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122317, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122317, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122318 q = 1) (hb : d123889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122318, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122318, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122319 q = 1) (hb : d123890 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122319, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122319, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122327 q = 1) (hb : d123898 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122327, d123898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122327, d123898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22133 (p : Pattern) (ha : d122333 p = 1) (hb : d123904 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d122321 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22130 q ha hb
    | true =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122322 q = 1) (hb : d123893 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122322, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122322, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d122323 q = 1) (hb : d123894 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122323, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122323, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122324 q = 1) (hb : d123895 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122324, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122324, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122325 q = 1) (hb : d123896 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122325, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122325, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d122328 q = 1) (hb : d123899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122328, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22132 q ha hb
    | true =>
      simp only [d122328, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d122329 q = 1) (hb : d123900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122329, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d122329, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d122330 q = 1) (hb : d123901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122330, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d122330, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d122331 q = 1) (hb : d123902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122331, d123902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d122331, d123902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d122332 q = 1) (hb : d123903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122332, d123903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d122332, d123903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d122333 q = 1) (hb : d123904 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122333, d123904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122333, d123904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro22134 (p : Pattern) (ha : d122340 p = 1) (hb : d123911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122328 q = 1) (hb : d123899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122328, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22132 q ha hb
    | true =>
      simp only [d122328, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122329 q = 1) (hb : d123900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122329, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122329, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d122330 q = 1) (hb : d123901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122330, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122330, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122338 q = 1) (hb : d123909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122338, d123909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122338, d123909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122339 q = 1) (hb : d123910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122339, d123910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122339, d123910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122340 q = 1) (hb : d123911 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122340, d123911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122340, d123911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22135 (p : Pattern) (ha : d122347 p = 1) (hb : d123917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14019 q = 1) (hb : d122346 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14019, d122346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14019, d122346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122347 q = 1) (hb : d123917 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122347, d123917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122347, d123917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro22136 (p : Pattern) (ha : d122353 p = 1) (hb : d123923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122348 q = 1) (hb : d123918 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122348, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22135 q ha hb
    | true =>
      simp only [d122348, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h2 (q : Pattern) (ha : d122349 q = 1) (hb : d123919 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122349, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122349, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122350 q = 1) (hb : d123920 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122350, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122350, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122351 q = 1) (hb : d123921 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122351, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122351, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d122352 q = 1) (hb : d123922 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122352, d123922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122352, d123922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122353 q = 1) (hb : d123923 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122353, d123923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122353, d123923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22137 (p : Pattern) (ha : d122359 p = 1) (hb : d123929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122354 q = 1) (hb : d123924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122354, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22136 q ha hb
    | true =>
      simp only [d122354, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122355 q = 1) (hb : d123925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122355, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122355, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122356 q = 1) (hb : d123926 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122356, d123926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122356, d123926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122357 q = 1) (hb : d123927 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122357, d123927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122357, d123927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122358 q = 1) (hb : d123928 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122358, d123928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122358, d123928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122359 q = 1) (hb : d123929 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122359, d123929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122359, d123929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22138 (p : Pattern) (ha : d122365 p = 1) (hb : d123935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122360 q = 1) (hb : d123930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122360, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22137 q ha hb
    | true =>
      simp only [d122360, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122361 q = 1) (hb : d123931 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122361, d123931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122361, d123931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d122362 q = 1) (hb : d123932 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122362, d123932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122362, d123932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122363 q = 1) (hb : d123933 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122363, d123933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122363, d123933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122364 q = 1) (hb : d123934 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122364, d123934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122364, d123934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122365 q = 1) (hb : d123935 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122365, d123935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122365, d123935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22139 (p : Pattern) (ha : d122371 p = 1) (hb : d123941 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d122334 q = 1) (hb : d123905 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122334, d123905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22131 q ha hb
    | true =>
      simp only [d122334, d123905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22133 q ha hb
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
  have h8 (q : Pattern) (ha : d122335 q = 1) (hb : d123906 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122335, d123906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122335, d123906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122336 q = 1) (hb : d123907 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122336, d123907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122336, d123907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122337 q = 1) (hb : d123908 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122337, d123908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d122337, d123908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122341 q = 1) (hb : d123912 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122341, d123912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122341, d123912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22134 q ha hb
  have h12 (q : Pattern) (ha : d122342 q = 1) (hb : d123913 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122342, d123913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122342, d123913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122343 q = 1) (hb : d123914 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122343, d123914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122343, d123914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122344 q = 1) (hb : d123915 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122344, d123915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122344, d123915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122345 q = 1) (hb : d123916 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122345, d123916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122345, d123916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122366 q = 1) (hb : d123936 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122366, d123936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122366, d123936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22138 q ha hb
  have h17 (q : Pattern) (ha : d122367 q = 1) (hb : d123937 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122367, d123937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122367, d123937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d122368 q = 1) (hb : d123938 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122368, d123938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122368, d123938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d122369 q = 1) (hb : d123939 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122369, d123939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d122369, d123939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d122370 q = 1) (hb : d123940 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122370, d123940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122370, d123940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122371 q = 1) (hb : d123941 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122371, d123941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122371, d123941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro22140 (p : Pattern) (ha : d122381 p = 1) (hb : d123951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122321 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22130 q ha hb
    | true =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d122377 q = 1) (hb : d123947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122377, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122377, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122378 q = 1) (hb : d123948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122378, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122378, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122379 q = 1) (hb : d123949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122379, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122379, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122380 q = 1) (hb : d123950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122380, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122380, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122381 q = 1) (hb : d123951 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122381, d123951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122381, d123951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22141 (p : Pattern) (ha : d122388 p = 1) (hb : d123958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122321 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22130 q ha hb
    | true =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d122377 q = 1) (hb : d123947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122377, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122377, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122378 q = 1) (hb : d123948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122378, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122378, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122379 q = 1) (hb : d123949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122379, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122379, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122380 q = 1) (hb : d123950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122380, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122380, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122328 q = 1) (hb : d123899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122328, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22132 q ha hb
    | true =>
      simp only [d122328, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d122384 q = 1) (hb : d123954 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122384, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122384, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122385 q = 1) (hb : d123955 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122385, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122385, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122386 q = 1) (hb : d123956 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122386, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122386, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122387 q = 1) (hb : d123957 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122387, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122387, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122388 q = 1) (hb : d123958 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122388, d123958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122388, d123958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22142 (p : Pattern) (ha : d122393 p = 1) (hb : d123963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22129 q ha hb
    | true =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122317 q = 1) (hb : d123888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122317, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122317, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122318 q = 1) (hb : d123889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122318, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122318, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122392 q = 1) (hb : d123962 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122392, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122392, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122393 q = 1) (hb : d123963 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122393, d123963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122393, d123963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22143 (p : Pattern) (ha : d122400 p = 1) (hb : d123970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22129 q ha hb
    | true =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122317 q = 1) (hb : d123888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122317, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122317, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122398 q = 1) (hb : d123968 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122398, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122398, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122399 q = 1) (hb : d123969 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122399, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122399, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122400 q = 1) (hb : d123970 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122400, d123970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122400, d123970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22144 (p : Pattern) (ha : d122406 p = 1) (hb : d123974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14077 q = 1) (hb : d122404 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14077, d122404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14077, d122404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122405 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122406 q = 1) (hb : d123974 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122406, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d122406, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro22145 (p : Pattern) (ha : d122412 p = 1) (hb : d123980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122407 q = 1) (hb : d123975 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122407, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22144 q ha hb
    | true =>
      simp only [d122407, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22128 q ha hb
  have h2 (q : Pattern) (ha : d122408 q = 1) (hb : d123976 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122408, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122408, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122409 q = 1) (hb : d123977 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122409, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122409, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122311 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122410 q = 1) (hb : d123978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122410, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122410, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122309 q = 1) (hb : d123880 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122309, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22128 q ha hb
    | true =>
      simp only [d122309, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h7 (q : Pattern) (ha : d122310 q = 1) (hb : d123881 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122310, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122310, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122311 q = 1) (hb : d123882 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122311, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122311, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122312 q = 1) (hb : d123883 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122312, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122312, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122411 q = 1) (hb : d123979 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122411, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122411, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122412 q = 1) (hb : d123980 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122412, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122412, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro22146 (p : Pattern) (ha : d122418 p = 1) (hb : d123986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122413 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122413, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22145 q ha hb
    | true =>
      simp only [d122413, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122414 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122414, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122414, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122315 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22129 q ha hb
    | true =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122316 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122415 q = 1) (hb : d123983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122415, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122415, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122416 q = 1) (hb : d123984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122416, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122416, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122417 q = 1) (hb : d123985 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122417, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122417, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122418 q = 1) (hb : d123986 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122418, d123986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122418, d123986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22147 (p : Pattern) (ha : d122424 p = 1) (hb : d123992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22129 q ha hb
    | true =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122421 q = 1) (hb : d123989 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122421, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122421, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122422 q = 1) (hb : d123990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122422, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122422, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122423 q = 1) (hb : d123991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122423, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122423, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122424 q = 1) (hb : d123992 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122424, d123992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122424, d123992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22148 (p : Pattern) (ha : d122430 p = 1) (hb : d123998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122394 q = 1) (hb : d123964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122394, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22142 q ha hb
    | true =>
      simp only [d122394, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d122395 q = 1) (hb : d123965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122395, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122395, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122396 q = 1) (hb : d123966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122396, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122396, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122397 q = 1) (hb : d123967 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122397, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122397, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122401 q = 1) (hb : d123971 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122401, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22143 q ha hb
    | true =>
      simp only [d122401, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d122402 q = 1) (hb : d123972 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122402, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122402, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122403 q = 1) (hb : d123973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122403, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122403, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122419 q = 1) (hb : d123987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122419, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22146 q ha hb
    | true =>
      simp only [d122419, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22130 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122420 q = 1) (hb : d123988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122420, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122420, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122425 q = 1) (hb : d123993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122425, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22147 q ha hb
    | true =>
      simp only [d122425, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122426 q = 1) (hb : d123994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122426, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122426, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122427 q = 1) (hb : d123995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122427, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122427, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122428 q = 1) (hb : d123996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122428, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122428, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122429 q = 1) (hb : d123997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122429, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122429, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122430 q = 1) (hb : d123998 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122430, d123998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122430, d123998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22149 (p : Pattern) (ha : d122431 p = 1) (hb : d123999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22129 q ha hb
    | true =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122317 q = 1) (hb : d123888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122317, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122317, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122318 q = 1) (hb : d123889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122318, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122318, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122392 q = 1) (hb : d123962 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122392, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122392, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122431 q = 1) (hb : d123999 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122431, d123999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122431, d123999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22150 (p : Pattern) (ha : d122436 p = 1) (hb : d124004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22129 q ha hb
    | true =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d122317 q = 1) (hb : d123888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122317, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122317, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122398 q = 1) (hb : d123968 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122398, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122398, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122399 q = 1) (hb : d123969 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122399, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122399, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122436 q = 1) (hb : d124004 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122436, d124004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122436, d124004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22151 (p : Pattern) (ha : d122440 p = 1) (hb : d124008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122413 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122413, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22145 q ha hb
    | true =>
      simp only [d122413, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122414 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122414, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122414, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122315 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22129 q ha hb
    | true =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122316 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122415 q = 1) (hb : d123983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122415, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122415, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122416 q = 1) (hb : d123984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122416, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122416, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122417 q = 1) (hb : d123985 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122417, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122417, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122440 q = 1) (hb : d124008 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122440, d124008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122440, d124008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22152 (p : Pattern) (ha : d122443 p = 1) (hb : d124011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122315 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22129 q ha hb
    | true =>
      simp only [d122315, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122316 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122316, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122421 q = 1) (hb : d123989 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122421, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122421, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122422 q = 1) (hb : d123990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122422, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122422, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122423 q = 1) (hb : d123991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122423, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122423, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122443 q = 1) (hb : d124011 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122443, d124011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122443, d124011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22153 (p : Pattern) (ha : d122449 p = 1) (hb : d124017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122394 q = 1) (hb : d123964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122394, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22142 q ha hb
    | true =>
      simp only [d122394, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d122395 q = 1) (hb : d123965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122395, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122395, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122396 q = 1) (hb : d123966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122396, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122396, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122397 q = 1) (hb : d123967 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122397, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122397, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122401 q = 1) (hb : d123971 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122401, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22143 q ha hb
    | true =>
      simp only [d122401, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d122402 q = 1) (hb : d123972 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122402, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122402, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122403 q = 1) (hb : d123973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122403, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122403, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122419 q = 1) (hb : d123987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122419, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22146 q ha hb
    | true =>
      simp only [d122419, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22130 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122420 q = 1) (hb : d123988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122420, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122420, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122425 q = 1) (hb : d123993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122425, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22147 q ha hb
    | true =>
      simp only [d122425, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122426 q = 1) (hb : d123994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122426, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122426, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122427 q = 1) (hb : d123995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122427, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122427, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122428 q = 1) (hb : d123996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122428, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122428, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122429 q = 1) (hb : d123997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122429, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122429, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122432 q = 1) (hb : d124000 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122432, d124000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22149 q ha hb
    | true =>
      simp only [d122432, d124000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d122433 q = 1) (hb : d124001 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122433, d124001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122433, d124001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122434 q = 1) (hb : d124002 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122434, d124002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122434, d124002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d122435 q = 1) (hb : d124003 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122435, d124003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122435, d124003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d122437 q = 1) (hb : d124005 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122437, d124005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22150 q ha hb
    | true =>
      simp only [d122437, d124005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d122438 q = 1) (hb : d124006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122438, d124006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122438, d124006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d122439 q = 1) (hb : d124007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122439, d124007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d122439, d124007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122441 q = 1) (hb : d124009 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122441, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22151 q ha hb
    | true =>
      simp only [d122441, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22132 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d122328 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d122442 q = 1) (hb : d124010 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122442, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d122442, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d122444 q = 1) (hb : d124012 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122444, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22152 q ha hb
    | true =>
      simp only [d122444, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d122445 q = 1) (hb : d124013 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122445, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d122445, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d122446 q = 1) (hb : d124014 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122446, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d122446, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122447 q = 1) (hb : d124015 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122447, d124015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d122447, d124015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d122448 q = 1) (hb : d124016 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122448, d124016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122448, d124016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d122449 q = 1) (hb : d124017 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122449, d124017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122449, d124017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro22154 (p : Pattern) (ha : d122451 p = 1) (hb : d124019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122321 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22130 q ha hb
    | true =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d122377 q = 1) (hb : d123947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122377, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122377, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122378 q = 1) (hb : d123948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122378, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122378, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122379 q = 1) (hb : d123949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122379, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122379, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122380 q = 1) (hb : d123950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122380, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122380, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d122451 q = 1) (hb : d124019 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122451, d124019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122451, d124019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro22155 (p : Pattern) (ha : d122458 p = 1) (hb : d124026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122441 q = 1) (hb : d124009 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122441, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22151 q ha hb
    | true =>
      simp only [d122441, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22132 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122328 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122442 q = 1) (hb : d124010 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122442, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122442, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122444 q = 1) (hb : d124012 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122444, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22152 q ha hb
    | true =>
      simp only [d122444, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122445 q = 1) (hb : d124013 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122445, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122445, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122446 q = 1) (hb : d124014 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122446, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122446, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122456 q = 1) (hb : d124024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122456, d124024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122456, d124024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122457 q = 1) (hb : d124025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122457, d124025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122457, d124025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122458 q = 1) (hb : d124026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122458, d124026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122458, d124026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22156 (p : Pattern) (ha : d122466 p = 1) (hb : d124032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14154 q = 1) (hb : d122464 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14154, d122464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14154, d122464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d122465 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122466 q = 1) (hb : d124032 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122466, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122466, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro22157 (p : Pattern) (ha : d122472 p = 1) (hb : d124038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122467 q = 1) (hb : d124033 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122467, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22156 q ha hb
    | true =>
      simp only [d122467, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22135 q ha hb
  have h2 (q : Pattern) (ha : d122468 q = 1) (hb : d124034 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122468, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122468, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122469 q = 1) (hb : d124035 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122469, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122469, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122350 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122470 q = 1) (hb : d124036 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122470, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122470, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122348 q = 1) (hb : d123918 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122348, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22135 q ha hb
    | true =>
      simp only [d122348, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h7 (q : Pattern) (ha : d122349 q = 1) (hb : d123919 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122349, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122349, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122350 q = 1) (hb : d123920 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122350, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122350, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122351 q = 1) (hb : d123921 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122351, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122351, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122471 q = 1) (hb : d124037 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122471, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122471, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122472 q = 1) (hb : d124038 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122472, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122472, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro22158 (p : Pattern) (ha : d122478 p = 1) (hb : d124044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122473 q = 1) (hb : d124039 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122473, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22157 q ha hb
    | true =>
      simp only [d122473, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122474 q = 1) (hb : d124040 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122474, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122474, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122354 q = 1) (hb : d123924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122354, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22136 q ha hb
    | true =>
      simp only [d122354, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122355 q = 1) (hb : d123925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122355, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122355, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122475 q = 1) (hb : d124041 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122475, d124041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122475, d124041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122476 q = 1) (hb : d124042 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122476, d124042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122476, d124042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122477 q = 1) (hb : d124043 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122477, d124043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122477, d124043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122478 q = 1) (hb : d124044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122478, d124044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122478, d124044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22159 (p : Pattern) (ha : d122484 p = 1) (hb : d124050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122354 q = 1) (hb : d123924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122354, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22136 q ha hb
    | true =>
      simp only [d122354, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122355 q = 1) (hb : d123925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122355, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122355, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122481 q = 1) (hb : d124047 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122481, d124047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122481, d124047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122482 q = 1) (hb : d124048 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122482, d124048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122482, d124048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122483 q = 1) (hb : d124049 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122483, d124049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122483, d124049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122484 q = 1) (hb : d124050 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122484, d124050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122484, d124050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22160 (p : Pattern) (ha : d122490 p = 1) (hb : d124056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122479 q = 1) (hb : d124045 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122479, d124045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22158 q ha hb
    | true =>
      simp only [d122479, d124045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22137 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122480 q = 1) (hb : d124046 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122480, d124046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122480, d124046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122485 q = 1) (hb : d124051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122485, d124051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22159 q ha hb
    | true =>
      simp only [d122485, d124051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122486 q = 1) (hb : d124052 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122486, d124052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122486, d124052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122487 q = 1) (hb : d124053 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122487, d124053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122487, d124053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122488 q = 1) (hb : d124054 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122488, d124054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122488, d124054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122489 q = 1) (hb : d124055 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122489, d124055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122489, d124055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122490 q = 1) (hb : d124056 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122490, d124056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122490, d124056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22161 (p : Pattern) (ha : d122496 p = 1) (hb : d124062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122382 q = 1) (hb : d123952 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122382, d123952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122382, d123952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22140 q ha hb
  have h2 (q : Pattern) (ha : d122383 q = 1) (hb : d123953 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122383, d123953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122383, d123953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122389 q = 1) (hb : d123959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122389, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22140 q ha hb
    | true =>
      simp only [d122389, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22141 q ha hb
  have h4 (q : Pattern) (ha : d122390 q = 1) (hb : d123960 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122390, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122390, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122391 q = 1) (hb : d123961 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122391, d123961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122391, d123961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122450 q = 1) (hb : d124018 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122450, d124018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22148 q ha hb
    | true =>
      simp only [d122450, d124018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22153 q ha hb
  have h7 (q : Pattern) (ha : d122452 q = 1) (hb : d124020 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122452, d124020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22154 q ha hb
    | true =>
      simp only [d122452, d124020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d122453 q = 1) (hb : d124021 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122453, d124021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122453, d124021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122454 q = 1) (hb : d124022 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122454, d124022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122454, d124022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122455 q = 1) (hb : d124023 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122455, d124023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122455, d124023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122459 q = 1) (hb : d124027 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122459, d124027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122459, d124027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22155 q ha hb
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
  have h13 (q : Pattern) (ha : d122460 q = 1) (hb : d124028 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122460, d124028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122460, d124028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122461 q = 1) (hb : d124029 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122461, d124029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122461, d124029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122462 q = 1) (hb : d124030 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122462, d124030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d122462, d124030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122463 q = 1) (hb : d124031 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122463, d124031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122463, d124031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122491 q = 1) (hb : d124057 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122491, d124057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122491, d124057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22160 q ha hb
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
  have h19 (q : Pattern) (ha : d122492 q = 1) (hb : d124058 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122492, d124058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122492, d124058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d122493 q = 1) (hb : d124059 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122493, d124059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122493, d124059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122494 q = 1) (hb : d124060 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122494, d124060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d122494, d124060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122495 q = 1) (hb : d124061 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122495, d124061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d122495, d124061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122496 q = 1) (hb : d124062 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122496, d124062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122496, d124062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro22162 (p : Pattern) (ha : d122502 p = 1) (hb : d124068 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d122372 q = 1) (hb : d123942 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122372, d123942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122372, d123942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22139 q ha hb
  have h6 (q : Pattern) (ha : d122373 q = 1) (hb : d123943 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122373, d123943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122373, d123943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122374 q = 1) (hb : d123944 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122374, d123944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122374, d123944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122375 q = 1) (hb : d123945 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122375, d123945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122375, d123945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122376 q = 1) (hb : d123946 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122376, d123946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122376, d123946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122497 q = 1) (hb : d124063 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122497, d124063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122497, d124063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22161 q ha hb
  have h11 (q : Pattern) (ha : d122498 q = 1) (hb : d124064 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122498, d124064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122498, d124064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122499 q = 1) (hb : d124065 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122499, d124065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122499, d124065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122500 q = 1) (hb : d124066 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122500, d124066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122500, d124066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122501 q = 1) (hb : d124067 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122501, d124067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122501, d124067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122502 q = 1) (hb : d124068 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122502, d124068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122502, d124068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro22163 (p : Pattern) (ha : d122505 p = 1) (hb : d123980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122407 q = 1) (hb : d123975 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122407, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22144 q ha hb
    | true =>
      simp only [d122407, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22128 q ha hb
  have h2 (q : Pattern) (ha : d122408 q = 1) (hb : d123976 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122408, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122408, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122409 q = 1) (hb : d123977 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122409, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122409, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122311 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122410 q = 1) (hb : d123978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122410, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122410, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122309 q = 1) (hb : d123880 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122309, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22128 q ha hb
    | true =>
      simp only [d122309, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h7 (q : Pattern) (ha : d122310 q = 1) (hb : d123881 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122310, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122310, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122311 q = 1) (hb : d123882 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122311, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122311, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122503 q = 1) (hb : d123883 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122503, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122503, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122504 q = 1) (hb : d123979 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122504, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122504, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122505 q = 1) (hb : d123980 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122505, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122505, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22164 (p : Pattern) (ha : d122509 p = 1) (hb : d124070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122309 q = 1) (hb : d123880 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122309, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22128 q ha hb
    | true =>
      simp only [d122309, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h2 (q : Pattern) (ha : d122310 q = 1) (hb : d123881 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122310, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122310, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122311 q = 1) (hb : d123882 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122311, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122311, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122503 q = 1) (hb : d123883 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122503, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122503, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122508 q = 1) (hb : d124069 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122508, d124069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122508, d124069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122509 q = 1) (hb : d124070 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122509, d124070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122509, d124070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22165 (p : Pattern) (ha : d122515 p = 1) (hb : d124076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22163 q ha hb
    | true =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122510 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22164 q ha hb
    | true =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122511 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122512 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122512, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122512, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122513 q = 1) (hb : d124074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122513, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122513, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122514 q = 1) (hb : d124075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122514, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122514, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122515 q = 1) (hb : d124076 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122515, d124076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122515, d124076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22166 (p : Pattern) (ha : d122519 p = 1) (hb : d124080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122510 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22164 q ha hb
    | true =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122511 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122516 q = 1) (hb : d124077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122516, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122516, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122517 q = 1) (hb : d124078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122517, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122517, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122518 q = 1) (hb : d124079 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122518, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122518, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122519 q = 1) (hb : d124080 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122519, d124080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122519, d124080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22167 (p : Pattern) (ha : d122525 p = 1) (hb : d124086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122520 q = 1) (hb : d124081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122520, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22165 q ha hb
    | true =>
      simp only [d122520, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22166 q ha hb
  have h2 (q : Pattern) (ha : d122521 q = 1) (hb : d124082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122521, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122521, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122522 q = 1) (hb : d124083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122522, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122522, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122523 q = 1) (hb : d124084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122523, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122523, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122524 q = 1) (hb : d124085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122524, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122524, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122525 q = 1) (hb : d124086 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122525, d124086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122525, d124086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22168 (p : Pattern) (ha : d122528 p = 1) (hb : d124089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22163 q ha hb
    | true =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122510 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22164 q ha hb
    | true =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122511 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122512 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122512, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122512, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122513 q = 1) (hb : d124074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122513, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122513, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122514 q = 1) (hb : d124075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122514, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122514, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122528 q = 1) (hb : d124089 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122528, d124089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122528, d124089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22169 (p : Pattern) (ha : d122529 p = 1) (hb : d124090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122510 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22164 q ha hb
    | true =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122511 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122516 q = 1) (hb : d124077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122516, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122516, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122517 q = 1) (hb : d124078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122517, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122517, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122518 q = 1) (hb : d124079 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122518, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122518, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122529 q = 1) (hb : d124090 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122529, d124090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122529, d124090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22170 (p : Pattern) (ha : d122535 p = 1) (hb : d124096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122520 q = 1) (hb : d124081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122520, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22165 q ha hb
    | true =>
      simp only [d122520, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22166 q ha hb
  have h2 (q : Pattern) (ha : d122521 q = 1) (hb : d124082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122521, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122521, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122522 q = 1) (hb : d124083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122522, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122522, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122523 q = 1) (hb : d124084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122523, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122523, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122524 q = 1) (hb : d124085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122524, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122524, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122530 q = 1) (hb : d124091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122530, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22168 q ha hb
    | true =>
      simp only [d122530, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22169 q ha hb
  have h7 (q : Pattern) (ha : d122531 q = 1) (hb : d124092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122531, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122531, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122532 q = 1) (hb : d124093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122532, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122532, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122533 q = 1) (hb : d124094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122533, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122533, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122534 q = 1) (hb : d124095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122534, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122534, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122535 q = 1) (hb : d124096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122535, d124096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122535, d124096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22171 (p : Pattern) (ha : d122540 p = 1) (hb : d124101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22163 q ha hb
    | true =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122510 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22164 q ha hb
    | true =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122511 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122512 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122512, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122512, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122513 q = 1) (hb : d124074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122513, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122513, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122539 q = 1) (hb : d124100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122539, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122539, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122540 q = 1) (hb : d124101 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122540, d124101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122540, d124101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22172 (p : Pattern) (ha : d122542 p = 1) (hb : d124103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122510 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22164 q ha hb
    | true =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122511 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122516 q = 1) (hb : d124077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122516, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122516, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122517 q = 1) (hb : d124078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122517, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122517, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122541 q = 1) (hb : d124102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122541, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122541, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122542 q = 1) (hb : d124103 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122542, d124103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122542, d124103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22173 (p : Pattern) (ha : d122549 p = 1) (hb : d124110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22163 q ha hb
    | true =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122510 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22164 q ha hb
    | true =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122511 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122512 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122512, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122512, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122547 q = 1) (hb : d124108 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122547, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122547, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122548 q = 1) (hb : d124109 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122548, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122548, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122549 q = 1) (hb : d124110 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122549, d124110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122549, d124110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22174 (p : Pattern) (ha : d122552 p = 1) (hb : d124113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122510 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22164 q ha hb
    | true =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122511 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122516 q = 1) (hb : d124077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122516, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122516, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122550 q = 1) (hb : d124111 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122550, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122550, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122551 q = 1) (hb : d124112 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122551, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122551, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122552 q = 1) (hb : d124113 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122552, d124113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122552, d124113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22175 (p : Pattern) (ha : d122558 p = 1) (hb : d124117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14261 q = 1) (hb : d122556 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14261, d122556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14261, d122556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122557 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122558 q = 1) (hb : d124117 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122558, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d122558, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro22176 (p : Pattern) (ha : d122568 p = 1) (hb : d124123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122559 q = 1) (hb : d124118 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122559, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22175 q ha hb
    | true =>
      simp only [d122559, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22144 q ha hb
  have h2 (q : Pattern) (ha : d122560 q = 1) (hb : d124119 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122560, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122560, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122561 q = 1) (hb : d124120 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122561, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122561, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122565 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122566 q = 1) (hb : d124121 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122566, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122566, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122407 q = 1) (hb : d123975 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122407, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22144 q ha hb
    | true =>
      simp only [d122407, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22128 q ha hb
  have h7 (q : Pattern) (ha : d122408 q = 1) (hb : d123976 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122408, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122408, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122409 q = 1) (hb : d123977 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122409, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122409, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122311 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122410 q = 1) (hb : d123978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122410, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122410, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122567 q = 1) (hb : d124122 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122567, d124122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122567, d124122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122568 q = 1) (hb : d124123 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122568, d124123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122568, d124123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro22177 (p : Pattern) (ha : d122574 p = 1) (hb : d124129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122569 q = 1) (hb : d124124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122569, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22176 q ha hb
    | true =>
      simp only [d122569, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122570 q = 1) (hb : d124125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122570, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122570, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122506 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22163 q ha hb
    | true =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122507 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122571 q = 1) (hb : d124126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122571, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122571, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122572 q = 1) (hb : d124127 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122572, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122572, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122573 q = 1) (hb : d124128 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122573, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122573, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122574 q = 1) (hb : d124129 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122574, d124129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122574, d124129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22178 (p : Pattern) (ha : d122580 p = 1) (hb : d124135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22163 q ha hb
    | true =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122577 q = 1) (hb : d124132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122577, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122577, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122578 q = 1) (hb : d124133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122578, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122578, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122579 q = 1) (hb : d124134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122579, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122579, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122580 q = 1) (hb : d124135 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122580, d124135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122580, d124135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22179 (p : Pattern) (ha : d122586 p = 1) (hb : d124141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122543 q = 1) (hb : d124104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122543, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22171 q ha hb
    | true =>
      simp only [d122543, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22172 q ha hb
  have h2 (q : Pattern) (ha : d122544 q = 1) (hb : d124105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122544, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122544, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122545 q = 1) (hb : d124106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122545, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122545, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122546 q = 1) (hb : d124107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122546, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122546, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122553 q = 1) (hb : d124114 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122553, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22173 q ha hb
    | true =>
      simp only [d122553, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22174 q ha hb
  have h6 (q : Pattern) (ha : d122554 q = 1) (hb : d124115 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122554, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122554, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122555 q = 1) (hb : d124116 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122555, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122555, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122575 q = 1) (hb : d124130 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122575, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22177 q ha hb
    | true =>
      simp only [d122575, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22165 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122520 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122576 q = 1) (hb : d124131 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122576, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122576, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122581 q = 1) (hb : d124136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122581, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22178 q ha hb
    | true =>
      simp only [d122581, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122582 q = 1) (hb : d124137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122582, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122582, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122583 q = 1) (hb : d124138 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122583, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122583, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122584 q = 1) (hb : d124139 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122584, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122584, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122585 q = 1) (hb : d124140 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122585, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122585, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122586 q = 1) (hb : d124141 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122586, d124141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122586, d124141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22180 (p : Pattern) (ha : d122587 p = 1) (hb : d124142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22163 q ha hb
    | true =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122510 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22164 q ha hb
    | true =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122511 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122512 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122512, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122512, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122513 q = 1) (hb : d124074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122513, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122513, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122539 q = 1) (hb : d124100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122539, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122539, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122587 q = 1) (hb : d124142 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122587, d124142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122587, d124142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22181 (p : Pattern) (ha : d122588 p = 1) (hb : d124143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122510 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22164 q ha hb
    | true =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122511 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122516 q = 1) (hb : d124077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122516, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122516, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122517 q = 1) (hb : d124078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122517, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122517, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122541 q = 1) (hb : d124102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122541, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122541, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122588 q = 1) (hb : d124143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122588, d124143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122588, d124143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22182 (p : Pattern) (ha : d122593 p = 1) (hb : d124148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22163 q ha hb
    | true =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122510 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22164 q ha hb
    | true =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122511 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122512 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122512, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122512, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122547 q = 1) (hb : d124108 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122547, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122547, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122548 q = 1) (hb : d124109 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122548, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122548, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122593 q = 1) (hb : d124148 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122593, d124148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122593, d124148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22183 (p : Pattern) (ha : d122594 p = 1) (hb : d124149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122510 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22164 q ha hb
    | true =>
      simp only [d122510, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122511 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122511, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122516 q = 1) (hb : d124077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122516, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122516, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122550 q = 1) (hb : d124111 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122550, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122550, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122551 q = 1) (hb : d124112 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122551, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122551, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122594 q = 1) (hb : d124149 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122594, d124149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122594, d124149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22184 (p : Pattern) (ha : d122598 p = 1) (hb : d124153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122569 q = 1) (hb : d124124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122569, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22176 q ha hb
    | true =>
      simp only [d122569, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122570 q = 1) (hb : d124125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122570, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122570, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122506 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22163 q ha hb
    | true =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122507 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122571 q = 1) (hb : d124126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122571, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122571, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122572 q = 1) (hb : d124127 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122572, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122572, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122573 q = 1) (hb : d124128 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122573, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122573, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122598 q = 1) (hb : d124153 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122598, d124153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122598, d124153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22185 (p : Pattern) (ha : d122601 p = 1) (hb : d124156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122506 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22163 q ha hb
    | true =>
      simp only [d122506, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122507 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122507, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122577 q = 1) (hb : d124132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122577, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122577, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122578 q = 1) (hb : d124133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122578, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122578, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122579 q = 1) (hb : d124134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122579, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122579, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122601 q = 1) (hb : d124156 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122601, d124156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122601, d124156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22186 (p : Pattern) (ha : d122607 p = 1) (hb : d124162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122543 q = 1) (hb : d124104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122543, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22171 q ha hb
    | true =>
      simp only [d122543, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22172 q ha hb
  have h2 (q : Pattern) (ha : d122544 q = 1) (hb : d124105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122544, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122544, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122545 q = 1) (hb : d124106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122545, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122545, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122546 q = 1) (hb : d124107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122546, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122546, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122553 q = 1) (hb : d124114 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122553, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22173 q ha hb
    | true =>
      simp only [d122553, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22174 q ha hb
  have h6 (q : Pattern) (ha : d122554 q = 1) (hb : d124115 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122554, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122554, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122555 q = 1) (hb : d124116 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122555, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122555, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122575 q = 1) (hb : d124130 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122575, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22177 q ha hb
    | true =>
      simp only [d122575, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22165 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122520 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122576 q = 1) (hb : d124131 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122576, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122576, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122581 q = 1) (hb : d124136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122581, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22178 q ha hb
    | true =>
      simp only [d122581, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122582 q = 1) (hb : d124137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122582, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122582, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122583 q = 1) (hb : d124138 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122583, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122583, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122584 q = 1) (hb : d124139 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122584, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122584, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122585 q = 1) (hb : d124140 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122585, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122585, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122589 q = 1) (hb : d124144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122589, d124144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22180 q ha hb
    | true =>
      simp only [d122589, d124144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22181 q ha hb
  have h17 (q : Pattern) (ha : d122590 q = 1) (hb : d124145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122590, d124145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122590, d124145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122591 q = 1) (hb : d124146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122591, d124146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122591, d124146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d122592 q = 1) (hb : d124147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122592, d124147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122592, d124147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d122595 q = 1) (hb : d124150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122595, d124150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22182 q ha hb
    | true =>
      simp only [d122595, d124150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22183 q ha hb
  have h21 (q : Pattern) (ha : d122596 q = 1) (hb : d124151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122596, d124151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122596, d124151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d122597 q = 1) (hb : d124152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122597, d124152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d122597, d124152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122599 q = 1) (hb : d124154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122599, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22184 q ha hb
    | true =>
      simp only [d122599, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22168 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d122530 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d122600 q = 1) (hb : d124155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122600, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d122600, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d122602 q = 1) (hb : d124157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122602, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22185 q ha hb
    | true =>
      simp only [d122602, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d122603 q = 1) (hb : d124158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122603, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d122603, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d122604 q = 1) (hb : d124159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122604, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d122604, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122605 q = 1) (hb : d124160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122605, d124160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d122605, d124160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d122606 q = 1) (hb : d124161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122606, d124161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122606, d124161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d122607 q = 1) (hb : d124162 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122607, d124162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122607, d124162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro22187 (p : Pattern) (ha : d122614 p = 1) (hb : d124169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122520 q = 1) (hb : d124081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122520, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22165 q ha hb
    | true =>
      simp only [d122520, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22166 q ha hb
  have h2 (q : Pattern) (ha : d122521 q = 1) (hb : d124082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122521, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122521, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122522 q = 1) (hb : d124083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122522, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122522, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122523 q = 1) (hb : d124084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122523, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122523, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122524 q = 1) (hb : d124085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122524, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122524, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122609 q = 1) (hb : d124164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122609, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22166 q ha hb
    | true =>
      simp only [d122609, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122610 q = 1) (hb : d124165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122610, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122610, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122611 q = 1) (hb : d124166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122611, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122611, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122612 q = 1) (hb : d124167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122612, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122612, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122613 q = 1) (hb : d124168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122613, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122613, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122614 q = 1) (hb : d124169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122614, d124169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122614, d124169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22188 (p : Pattern) (ha : d122620 p = 1) (hb : d124175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122609 q = 1) (hb : d124164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122609, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22166 q ha hb
    | true =>
      simp only [d122609, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122610 q = 1) (hb : d124165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122610, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122610, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122611 q = 1) (hb : d124166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122611, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122611, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122612 q = 1) (hb : d124167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122612, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122612, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122613 q = 1) (hb : d124168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122613, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122613, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122615 q = 1) (hb : d124170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122615, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22169 q ha hb
    | true =>
      simp only [d122615, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122616 q = 1) (hb : d124171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122616, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122616, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122617 q = 1) (hb : d124172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122617, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122617, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122618 q = 1) (hb : d124173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122618, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122618, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122619 q = 1) (hb : d124174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122619, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122619, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122620 q = 1) (hb : d124175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122620, d124175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122620, d124175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22189 (p : Pattern) (ha : d122627 p = 1) (hb : d124182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122599 q = 1) (hb : d124154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122599, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22184 q ha hb
    | true =>
      simp only [d122599, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22168 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122530 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122600 q = 1) (hb : d124155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122600, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122600, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122602 q = 1) (hb : d124157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122602, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22185 q ha hb
    | true =>
      simp only [d122602, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122603 q = 1) (hb : d124158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122603, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122603, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122604 q = 1) (hb : d124159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122604, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122604, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122625 q = 1) (hb : d124180 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122625, d124180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122625, d124180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122626 q = 1) (hb : d124181 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122626, d124181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122626, d124181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122627 q = 1) (hb : d124182 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122627, d124182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122627, d124182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22190 (p : Pattern) (ha : d122629 p = 1) (hb : d124184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122615 q = 1) (hb : d124170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122615, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22169 q ha hb
    | true =>
      simp only [d122615, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122616 q = 1) (hb : d124171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122616, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122616, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122617 q = 1) (hb : d124172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122617, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122617, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122618 q = 1) (hb : d124173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122618, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122618, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122619 q = 1) (hb : d124174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122619, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122619, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122629 q = 1) (hb : d124184 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122629, d124184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122629, d124184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22191 (p : Pattern) (ha : d122637 p = 1) (hb : d124190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14370 q = 1) (hb : d122635 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14370, d122635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14370, d122635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d122636 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122637 q = 1) (hb : d124190 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122637, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122637, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro22192 (p : Pattern) (ha : d122647 p = 1) (hb : d124196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122638 q = 1) (hb : d124191 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122638, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22191 q ha hb
    | true =>
      simp only [d122638, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22156 q ha hb
  have h2 (q : Pattern) (ha : d122639 q = 1) (hb : d124192 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122639, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122639, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122640 q = 1) (hb : d124193 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122640, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122640, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122644 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122645 q = 1) (hb : d124194 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122645, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122645, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122467 q = 1) (hb : d124033 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122467, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22156 q ha hb
    | true =>
      simp only [d122467, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22135 q ha hb
  have h7 (q : Pattern) (ha : d122468 q = 1) (hb : d124034 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122468, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122468, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122469 q = 1) (hb : d124035 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122469, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122469, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122350 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122470 q = 1) (hb : d124036 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122470, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122470, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122646 q = 1) (hb : d124195 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122646, d124195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122646, d124195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122647 q = 1) (hb : d124196 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122647, d124196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122647, d124196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro22193 (p : Pattern) (ha : d122652 p = 1) (hb : d124038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122467 q = 1) (hb : d124033 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122467, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22156 q ha hb
    | true =>
      simp only [d122467, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22135 q ha hb
  have h2 (q : Pattern) (ha : d122468 q = 1) (hb : d124034 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122468, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122468, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122469 q = 1) (hb : d124035 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122469, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122469, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122350 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122470 q = 1) (hb : d124036 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122470, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122470, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122348 q = 1) (hb : d123918 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122348, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22135 q ha hb
    | true =>
      simp only [d122348, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h7 (q : Pattern) (ha : d122349 q = 1) (hb : d123919 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122349, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122349, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122350 q = 1) (hb : d123920 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122350, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122350, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122650 q = 1) (hb : d123921 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122650, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122650, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122651 q = 1) (hb : d124037 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122651, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122651, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122652 q = 1) (hb : d124038 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122652, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122652, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22194 (p : Pattern) (ha : d122658 p = 1) (hb : d124202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122648 q = 1) (hb : d124197 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122648, d124197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22192 q ha hb
    | true =>
      simp only [d122648, d124197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122649 q = 1) (hb : d124198 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122649, d124198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122649, d124198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122653 q = 1) (hb : d124039 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122653, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22193 q ha hb
    | true =>
      simp only [d122653, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122654 q = 1) (hb : d124040 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122654, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122654, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122655 q = 1) (hb : d124199 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122655, d124199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122655, d124199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122656 q = 1) (hb : d124200 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122656, d124200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122656, d124200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122657 q = 1) (hb : d124201 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122657, d124201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122657, d124201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122658 q = 1) (hb : d124202 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122658, d124202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122658, d124202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22195 (p : Pattern) (ha : d122660 p = 1) (hb : d124204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122348 q = 1) (hb : d123918 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122348, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22135 q ha hb
    | true =>
      simp only [d122348, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h2 (q : Pattern) (ha : d122349 q = 1) (hb : d123919 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122349, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122349, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122350 q = 1) (hb : d123920 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122350, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122350, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122650 q = 1) (hb : d123921 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122650, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122650, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122659 q = 1) (hb : d124203 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122659, d124203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122659, d124203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122660 q = 1) (hb : d124204 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122660, d124204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122660, d124204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22196 (p : Pattern) (ha : d122666 p = 1) (hb : d124210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122653 q = 1) (hb : d124039 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122653, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22193 q ha hb
    | true =>
      simp only [d122653, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122654 q = 1) (hb : d124040 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122654, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122654, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122661 q = 1) (hb : d124205 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122661, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22195 q ha hb
    | true =>
      simp only [d122661, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122662 q = 1) (hb : d124206 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122662, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122662, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122663 q = 1) (hb : d124207 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122663, d124207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122663, d124207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122664 q = 1) (hb : d124208 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122664, d124208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122664, d124208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122665 q = 1) (hb : d124209 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122665, d124209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122665, d124209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122666 q = 1) (hb : d124210 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122666, d124210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122666, d124210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22197 (p : Pattern) (ha : d122677 p = 1) (hb : d124216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122653 q = 1) (hb : d124039 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122653, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22193 q ha hb
    | true =>
      simp only [d122653, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122654 q = 1) (hb : d124040 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122654, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122654, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122674 q = 1) (hb : d124213 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122674, d124213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122674, d124213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122675 q = 1) (hb : d124214 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122675, d124214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122675, d124214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122676 q = 1) (hb : d124215 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122676, d124215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122676, d124215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122677 q = 1) (hb : d124216 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122677, d124216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122677, d124216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22198 (p : Pattern) (ha : d122683 p = 1) (hb : d124222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122667 q = 1) (hb : d124211 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122667, d124211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22194 q ha hb
    | true =>
      simp only [d122667, d124211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22196 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122673 q = 1) (hb : d124212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122673, d124212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122673, d124212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122678 q = 1) (hb : d124217 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122678, d124217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22197 q ha hb
    | true =>
      simp only [d122678, d124217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122679 q = 1) (hb : d124218 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122679, d124218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122679, d124218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122680 q = 1) (hb : d124219 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122680, d124219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122680, d124219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122681 q = 1) (hb : d124220 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122681, d124220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122681, d124220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122682 q = 1) (hb : d124221 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122682, d124221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122682, d124221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122683 q = 1) (hb : d124222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122683, d124222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122683, d124222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22199 (p : Pattern) (ha : d122671 p = 1) (hb : d124227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122661 q = 1) (hb : d124205 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122661, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22195 q ha hb
    | true =>
      simp only [d122661, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122662 q = 1) (hb : d124206 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122662, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122662, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122668 q = 1) (hb : d124224 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122668, d124224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122668, d124224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122669 q = 1) (hb : d124225 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122669, d124225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122669, d124225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122670 q = 1) (hb : d124226 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122670, d124226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122670, d124226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122671 q = 1) (hb : d124227 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122671, d124227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122671, d124227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22200 (p : Pattern) (ha : d122690 p = 1) (hb : d124233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122685 q = 1) (hb : d124228 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122685, d124228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22199 q ha hb
    | true =>
      simp only [d122685, d124228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122686 q = 1) (hb : d124229 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122686, d124229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122686, d124229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122687 q = 1) (hb : d124230 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122687, d124230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122687, d124230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122688 q = 1) (hb : d124231 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122688, d124231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122688, d124231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122689 q = 1) (hb : d124232 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122689, d124232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122689, d124232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122690 q = 1) (hb : d124233 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122690, d124233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122690, d124233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22201 (p : Pattern) (ha : d122696 p = 1) (hb : d124239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122526 q = 1) (hb : d124087 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122526, d124087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122526, d124087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22167 q ha hb
  have h2 (q : Pattern) (ha : d122527 q = 1) (hb : d124088 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122527, d124088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122527, d124088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122536 q = 1) (hb : d124097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122536, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22167 q ha hb
    | true =>
      simp only [d122536, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22170 q ha hb
  have h4 (q : Pattern) (ha : d122537 q = 1) (hb : d124098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122537, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122537, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122538 q = 1) (hb : d124099 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122538, d124099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122538, d124099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122608 q = 1) (hb : d124163 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122608, d124163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22179 q ha hb
    | true =>
      simp only [d122608, d124163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22186 q ha hb
  have h7 (q : Pattern) (ha : d122621 q = 1) (hb : d124176 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122621, d124176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22187 q ha hb
    | true =>
      simp only [d122621, d124176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22188 q ha hb
  have h8 (q : Pattern) (ha : d122622 q = 1) (hb : d124177 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122622, d124177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122622, d124177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122623 q = 1) (hb : d124178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122623, d124178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122623, d124178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122624 q = 1) (hb : d124179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122624, d124179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122624, d124179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122628 q = 1) (hb : d124183 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122628, d124183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122628, d124183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22189 q ha hb
  have h12 (q : Pattern) (ha : d122630 q = 1) (hb : d124185 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122630, d124185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122630, d124185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22190 q ha hb
  have h13 (q : Pattern) (ha : d122631 q = 1) (hb : d124186 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122631, d124186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122631, d124186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122632 q = 1) (hb : d124187 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122632, d124187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122632, d124187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122633 q = 1) (hb : d124188 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122633, d124188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d122633, d124188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122634 q = 1) (hb : d124189 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122634, d124189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122634, d124189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122684 q = 1) (hb : d124223 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122684, d124223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122684, d124223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22198 q ha hb
  have h18 (q : Pattern) (ha : d122691 q = 1) (hb : d124234 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122691, d124234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122691, d124234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22200 q ha hb
  have h19 (q : Pattern) (ha : d122692 q = 1) (hb : d124235 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122692, d124235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122692, d124235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d122693 q = 1) (hb : d124236 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122693, d124236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122693, d124236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122694 q = 1) (hb : d124237 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122694, d124237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d122694, d124237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122695 q = 1) (hb : d124238 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122695, d124238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d122695, d124238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122696 q = 1) (hb : d124239 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122696, d124239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122696, d124239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro22202 (p : Pattern) (ha : d122702 p = 1) (hb : d124245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122697 q = 1) (hb : d124240 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122697, d124240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122697, d124240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22201 q ha hb
  have h2 (q : Pattern) (ha : d122698 q = 1) (hb : d124241 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122698, d124241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122698, d124241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122699 q = 1) (hb : d124242 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122699, d124242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122699, d124242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122700 q = 1) (hb : d124243 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122700, d124243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122700, d124243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122701 q = 1) (hb : d124244 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122701, d124244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122701, d124244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122702 q = 1) (hb : d124245 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122702, d124245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122702, d124245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22203 (p : Pattern) (ha : d122704 p = 1) (hb : d123974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14077 q = 1) (hb : d122404 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14077, d122404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14077, d122404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122704 q = 1) (hb : d123974 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122704, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d122704, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro22204 (p : Pattern) (ha : d122714 p = 1) (hb : d124252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122705 q = 1) (hb : d124118 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122705, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22175 q ha hb
    | true =>
      simp only [d122705, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22203 q ha hb
  have h2 (q : Pattern) (ha : d122706 q = 1) (hb : d124119 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122706, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122706, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122707 q = 1) (hb : d124120 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122707, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122707, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122710 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122711 q = 1) (hb : d124121 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122711, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122711, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122708 q = 1) (hb : d124247 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122708, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22203 q ha hb
    | true =>
      simp only [d122708, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h7 (q : Pattern) (ha : d122709 q = 1) (hb : d124248 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122709, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122709, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122710 q = 1) (hb : d124249 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122710, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122710, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122712 q = 1) (hb : d124250 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122712, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122712, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122713 q = 1) (hb : d124251 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122713, d124251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122713, d124251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122714 q = 1) (hb : d124252 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122714, d124252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122714, d124252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22205 (p : Pattern) (ha : d122718 p = 1) (hb : d124256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122708 q = 1) (hb : d124247 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122708, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22203 q ha hb
    | true =>
      simp only [d122708, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h2 (q : Pattern) (ha : d122709 q = 1) (hb : d124248 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122709, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122709, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122710 q = 1) (hb : d124249 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122710, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122710, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122712 q = 1) (hb : d124250 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122712, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122712, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122717 q = 1) (hb : d124255 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122717, d124255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122717, d124255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122718 q = 1) (hb : d124256 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122718, d124256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122718, d124256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22206 (p : Pattern) (ha : d122724 p = 1) (hb : d124262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22204 q ha hb
    | true =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122719 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22205 q ha hb
    | true =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122720 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122721 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122721, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122721, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122722 q = 1) (hb : d124260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122722, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122722, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122723 q = 1) (hb : d124261 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122723, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122723, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122724 q = 1) (hb : d124262 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122724, d124262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122724, d124262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22207 (p : Pattern) (ha : d122728 p = 1) (hb : d124266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122719 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22205 q ha hb
    | true =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122720 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122725 q = 1) (hb : d124263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122725, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122725, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122726 q = 1) (hb : d124264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122726, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122726, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122727 q = 1) (hb : d124265 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122727, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122727, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122728 q = 1) (hb : d124266 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122728, d124266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122728, d124266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22208 (p : Pattern) (ha : d122734 p = 1) (hb : d124272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122729 q = 1) (hb : d124267 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122729, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22206 q ha hb
    | true =>
      simp only [d122729, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22207 q ha hb
  have h2 (q : Pattern) (ha : d122730 q = 1) (hb : d124268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122730, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122730, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122731 q = 1) (hb : d124269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122731, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122731, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122732 q = 1) (hb : d124270 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122732, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122732, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122733 q = 1) (hb : d124271 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122733, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122733, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122734 q = 1) (hb : d124272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122734, d124272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122734, d124272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22209 (p : Pattern) (ha : d122737 p = 1) (hb : d124275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22204 q ha hb
    | true =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122719 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22205 q ha hb
    | true =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122720 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122721 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122721, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122721, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122722 q = 1) (hb : d124260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122722, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122722, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122723 q = 1) (hb : d124261 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122723, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122723, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122737 q = 1) (hb : d124275 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122737, d124275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122737, d124275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22210 (p : Pattern) (ha : d122738 p = 1) (hb : d124276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122719 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22205 q ha hb
    | true =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122720 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122725 q = 1) (hb : d124263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122725, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122725, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122726 q = 1) (hb : d124264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122726, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122726, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122727 q = 1) (hb : d124265 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122727, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122727, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122738 q = 1) (hb : d124276 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122738, d124276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122738, d124276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22211 (p : Pattern) (ha : d122744 p = 1) (hb : d124282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122729 q = 1) (hb : d124267 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122729, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22206 q ha hb
    | true =>
      simp only [d122729, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22207 q ha hb
  have h2 (q : Pattern) (ha : d122730 q = 1) (hb : d124268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122730, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122730, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122731 q = 1) (hb : d124269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122731, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122731, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122732 q = 1) (hb : d124270 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122732, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122732, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122733 q = 1) (hb : d124271 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122733, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122733, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122739 q = 1) (hb : d124277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122739, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22209 q ha hb
    | true =>
      simp only [d122739, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22210 q ha hb
  have h7 (q : Pattern) (ha : d122740 q = 1) (hb : d124278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122740, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122740, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122741 q = 1) (hb : d124279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122741, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122741, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122742 q = 1) (hb : d124280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122742, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122742, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122743 q = 1) (hb : d124281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122743, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122743, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122744 q = 1) (hb : d124282 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122744, d124282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122744, d124282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22212 (p : Pattern) (ha : d122749 p = 1) (hb : d124287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22204 q ha hb
    | true =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122719 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22205 q ha hb
    | true =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122720 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122721 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122721, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122721, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122722 q = 1) (hb : d124260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122722, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122722, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122748 q = 1) (hb : d124286 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122748, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122748, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122749 q = 1) (hb : d124287 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122749, d124287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122749, d124287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22213 (p : Pattern) (ha : d122751 p = 1) (hb : d124289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122719 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22205 q ha hb
    | true =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122720 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122725 q = 1) (hb : d124263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122725, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122725, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122726 q = 1) (hb : d124264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122726, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122726, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122750 q = 1) (hb : d124288 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122750, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122750, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122751 q = 1) (hb : d124289 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122751, d124289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122751, d124289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22214 (p : Pattern) (ha : d122758 p = 1) (hb : d124296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22204 q ha hb
    | true =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122719 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22205 q ha hb
    | true =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122720 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122721 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122721, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122721, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122756 q = 1) (hb : d124294 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122756, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122756, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122757 q = 1) (hb : d124295 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122757, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122757, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122758 q = 1) (hb : d124296 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122758, d124296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122758, d124296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22215 (p : Pattern) (ha : d122761 p = 1) (hb : d124299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122719 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22205 q ha hb
    | true =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122720 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122725 q = 1) (hb : d124263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122725, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122725, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122759 q = 1) (hb : d124297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122759, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122759, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122760 q = 1) (hb : d124298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122760, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122760, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122761 q = 1) (hb : d124299 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122761, d124299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122761, d124299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22216 (p : Pattern) (ha : d122769 p = 1) (hb : d124303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d835 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d836 q = 1) (hb : d52513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d52514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d837, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14528 q = 1) (hb : d122765 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14528, d122765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14528, d122765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122768 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122769 q = 1) (hb : d124303 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122769, d124303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d122769, d124303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro22217 (p : Pattern) (ha : d122779 p = 1) (hb : d124309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122770 q = 1) (hb : d124304 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122770, d124304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22216 q ha hb
    | true =>
      simp only [d122770, d124304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22175 q ha hb
  have h2 (q : Pattern) (ha : d122771 q = 1) (hb : d124305 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122771, d124305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122771, d124305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122772 q = 1) (hb : d124306 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122772, d124306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122772, d124306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122776 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122777 q = 1) (hb : d124307 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122777, d124307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122777, d124307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122705 q = 1) (hb : d124118 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122705, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22175 q ha hb
    | true =>
      simp only [d122705, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22203 q ha hb
  have h7 (q : Pattern) (ha : d122706 q = 1) (hb : d124119 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122706, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122706, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122707 q = 1) (hb : d124120 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122707, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122707, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122710 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122711 q = 1) (hb : d124121 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122711, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122711, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122778 q = 1) (hb : d124308 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122778, d124308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122778, d124308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122779 q = 1) (hb : d124309 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122779, d124309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122779, d124309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro22218 (p : Pattern) (ha : d122785 p = 1) (hb : d124315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122780 q = 1) (hb : d124310 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122780, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22217 q ha hb
    | true =>
      simp only [d122780, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122781 q = 1) (hb : d124311 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122781, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122781, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122715 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22204 q ha hb
    | true =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122716 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122782 q = 1) (hb : d124312 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122782, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122782, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122783 q = 1) (hb : d124313 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122783, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122783, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122784 q = 1) (hb : d124314 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122784, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122784, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122785 q = 1) (hb : d124315 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122785, d124315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122785, d124315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22219 (p : Pattern) (ha : d122791 p = 1) (hb : d124321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22204 q ha hb
    | true =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122788 q = 1) (hb : d124318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122788, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122788, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122789 q = 1) (hb : d124319 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122789, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122789, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122790 q = 1) (hb : d124320 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122790, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122790, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122791 q = 1) (hb : d124321 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122791, d124321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122791, d124321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22220 (p : Pattern) (ha : d122797 p = 1) (hb : d124327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122752 q = 1) (hb : d124290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122752, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22212 q ha hb
    | true =>
      simp only [d122752, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22213 q ha hb
  have h2 (q : Pattern) (ha : d122753 q = 1) (hb : d124291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122753, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122753, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122754 q = 1) (hb : d124292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122754, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122754, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122755 q = 1) (hb : d124293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122755, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122755, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122762 q = 1) (hb : d124300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122762, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22214 q ha hb
    | true =>
      simp only [d122762, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22215 q ha hb
  have h6 (q : Pattern) (ha : d122763 q = 1) (hb : d124301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122763, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122763, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122764 q = 1) (hb : d124302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122764, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122764, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122786 q = 1) (hb : d124316 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122786, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22218 q ha hb
    | true =>
      simp only [d122786, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22206 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122729 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122787 q = 1) (hb : d124317 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122787, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122787, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122792 q = 1) (hb : d124322 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122792, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22219 q ha hb
    | true =>
      simp only [d122792, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122793 q = 1) (hb : d124323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122793, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122793, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122794 q = 1) (hb : d124324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122794, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122794, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122795 q = 1) (hb : d124325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122795, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122795, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122796 q = 1) (hb : d124326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122796, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122796, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122797 q = 1) (hb : d124327 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122797, d124327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122797, d124327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22221 (p : Pattern) (ha : d122798 p = 1) (hb : d124328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22204 q ha hb
    | true =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122719 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22205 q ha hb
    | true =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122720 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122721 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122721, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122721, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122722 q = 1) (hb : d124260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122722, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122722, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122748 q = 1) (hb : d124286 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122748, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122748, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122798 q = 1) (hb : d124328 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122798, d124328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122798, d124328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22222 (p : Pattern) (ha : d122799 p = 1) (hb : d124329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122719 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22205 q ha hb
    | true =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122720 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122725 q = 1) (hb : d124263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122725, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122725, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122726 q = 1) (hb : d124264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122726, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122726, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122750 q = 1) (hb : d124288 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122750, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122750, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122799 q = 1) (hb : d124329 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122799, d124329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122799, d124329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22223 (p : Pattern) (ha : d122804 p = 1) (hb : d124334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22204 q ha hb
    | true =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122719 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22205 q ha hb
    | true =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122720 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122721 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122721, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122721, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122756 q = 1) (hb : d124294 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122756, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122756, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122757 q = 1) (hb : d124295 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122757, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122757, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122804 q = 1) (hb : d124334 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122804, d124334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122804, d124334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22224 (p : Pattern) (ha : d122805 p = 1) (hb : d124335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122719 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22205 q ha hb
    | true =>
      simp only [d122719, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122720 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122725 q = 1) (hb : d124263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122725, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122725, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122759 q = 1) (hb : d124297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122759, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122759, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122760 q = 1) (hb : d124298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122760, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122760, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122805 q = 1) (hb : d124335 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122805, d124335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122805, d124335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22225 (p : Pattern) (ha : d122809 p = 1) (hb : d124339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122780 q = 1) (hb : d124310 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122780, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22217 q ha hb
    | true =>
      simp only [d122780, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122781 q = 1) (hb : d124311 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122781, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122781, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122715 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22204 q ha hb
    | true =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122716 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122782 q = 1) (hb : d124312 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122782, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122782, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122783 q = 1) (hb : d124313 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122783, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122783, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122784 q = 1) (hb : d124314 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122784, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122784, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122809 q = 1) (hb : d124339 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122809, d124339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122809, d124339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22226 (p : Pattern) (ha : d122812 p = 1) (hb : d124342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22204 q ha hb
    | true =>
      simp only [d122715, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122788 q = 1) (hb : d124318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122788, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122788, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122789 q = 1) (hb : d124319 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122789, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122789, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122790 q = 1) (hb : d124320 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122790, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122790, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122812 q = 1) (hb : d124342 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122812, d124342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122812, d124342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22227 (p : Pattern) (ha : d122818 p = 1) (hb : d124348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122752 q = 1) (hb : d124290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122752, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22212 q ha hb
    | true =>
      simp only [d122752, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22213 q ha hb
  have h2 (q : Pattern) (ha : d122753 q = 1) (hb : d124291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122753, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122753, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122754 q = 1) (hb : d124292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122754, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122754, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122755 q = 1) (hb : d124293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122755, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122755, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122762 q = 1) (hb : d124300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122762, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22214 q ha hb
    | true =>
      simp only [d122762, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22215 q ha hb
  have h6 (q : Pattern) (ha : d122763 q = 1) (hb : d124301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122763, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122763, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122764 q = 1) (hb : d124302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122764, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122764, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122786 q = 1) (hb : d124316 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122786, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22218 q ha hb
    | true =>
      simp only [d122786, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22206 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122729 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122787 q = 1) (hb : d124317 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122787, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122787, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122792 q = 1) (hb : d124322 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122792, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22219 q ha hb
    | true =>
      simp only [d122792, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122793 q = 1) (hb : d124323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122793, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122793, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122794 q = 1) (hb : d124324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122794, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122794, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122795 q = 1) (hb : d124325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122795, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122795, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122796 q = 1) (hb : d124326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122796, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122796, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122800 q = 1) (hb : d124330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122800, d124330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22221 q ha hb
    | true =>
      simp only [d122800, d124330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22222 q ha hb
  have h17 (q : Pattern) (ha : d122801 q = 1) (hb : d124331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122801, d124331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122801, d124331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122802 q = 1) (hb : d124332 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122802, d124332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122802, d124332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d122803 q = 1) (hb : d124333 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122803, d124333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122803, d124333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d122806 q = 1) (hb : d124336 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122806, d124336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22223 q ha hb
    | true =>
      simp only [d122806, d124336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22224 q ha hb
  have h21 (q : Pattern) (ha : d122807 q = 1) (hb : d124337 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122807, d124337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122807, d124337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d122808 q = 1) (hb : d124338 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122808, d124338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d122808, d124338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122810 q = 1) (hb : d124340 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122810, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22225 q ha hb
    | true =>
      simp only [d122810, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22209 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d122739 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d122811 q = 1) (hb : d124341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122811, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d122811, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d122813 q = 1) (hb : d124343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122813, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22226 q ha hb
    | true =>
      simp only [d122813, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d122814 q = 1) (hb : d124344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122814, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d122814, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d122815 q = 1) (hb : d124345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122815, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d122815, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122816 q = 1) (hb : d124346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122816, d124346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d122816, d124346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d122817 q = 1) (hb : d124347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122817, d124347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122817, d124347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d122818 q = 1) (hb : d124348 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122818, d124348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122818, d124348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro22228 (p : Pattern) (ha : d122825 p = 1) (hb : d124355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122729 q = 1) (hb : d124267 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122729, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22206 q ha hb
    | true =>
      simp only [d122729, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22207 q ha hb
  have h2 (q : Pattern) (ha : d122730 q = 1) (hb : d124268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122730, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122730, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122731 q = 1) (hb : d124269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122731, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122731, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122732 q = 1) (hb : d124270 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122732, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122732, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122733 q = 1) (hb : d124271 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122733, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122733, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122820 q = 1) (hb : d124350 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122820, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22207 q ha hb
    | true =>
      simp only [d122820, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122821 q = 1) (hb : d124351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122821, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122821, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122822 q = 1) (hb : d124352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122822, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122822, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122823 q = 1) (hb : d124353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122823, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122823, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122824 q = 1) (hb : d124354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122824, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122824, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122825 q = 1) (hb : d124355 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122825, d124355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122825, d124355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22229 (p : Pattern) (ha : d122831 p = 1) (hb : d124361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122820 q = 1) (hb : d124350 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122820, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22207 q ha hb
    | true =>
      simp only [d122820, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122821 q = 1) (hb : d124351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122821, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122821, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122822 q = 1) (hb : d124352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122822, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122822, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122823 q = 1) (hb : d124353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122823, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122823, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122824 q = 1) (hb : d124354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122824, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122824, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122826 q = 1) (hb : d124356 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122826, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22210 q ha hb
    | true =>
      simp only [d122826, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122827 q = 1) (hb : d124357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122827, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122827, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122828 q = 1) (hb : d124358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122828, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122828, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122829 q = 1) (hb : d124359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122829, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122829, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122830 q = 1) (hb : d124360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122830, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122830, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122831 q = 1) (hb : d124361 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122831, d124361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122831, d124361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22230 (p : Pattern) (ha : d122838 p = 1) (hb : d124368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122810 q = 1) (hb : d124340 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122810, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22225 q ha hb
    | true =>
      simp only [d122810, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22209 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122739 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122811 q = 1) (hb : d124341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122811, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122811, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122813 q = 1) (hb : d124343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122813, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22226 q ha hb
    | true =>
      simp only [d122813, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122814 q = 1) (hb : d124344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122814, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122814, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122815 q = 1) (hb : d124345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122815, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122815, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122836 q = 1) (hb : d124366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122836, d124366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122836, d124366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122837 q = 1) (hb : d124367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122837, d124367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122837, d124367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122838 q = 1) (hb : d124368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122838, d124368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122838, d124368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22231 (p : Pattern) (ha : d122840 p = 1) (hb : d124370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122826 q = 1) (hb : d124356 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122826, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22210 q ha hb
    | true =>
      simp only [d122826, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122827 q = 1) (hb : d124357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122827, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122827, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122828 q = 1) (hb : d124358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122828, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122828, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122829 q = 1) (hb : d124359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122829, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122829, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122830 q = 1) (hb : d124360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122830, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122830, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122840 q = 1) (hb : d124370 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122840, d124370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122840, d124370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22232 (p : Pattern) (ha : d122852 p = 1) (hb : d124376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d52584 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d966 q = 1) (hb : d52585 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d835 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d967 q = 1) (hb : d52586 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d967, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d968 q = 1) (hb : d52587 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d968, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14643 q = 1) (hb : d122846 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14643, d122846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14643, d122846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d122851 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122852 q = 1) (hb : d124376 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122852, d124376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122852, d124376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro22233 (p : Pattern) (ha : d122861 p = 1) (hb : d124032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14154 q = 1) (hb : d122464 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14154, d122464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14154, d122464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122861 q = 1) (hb : d124032 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122861, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122861, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro22234 (p : Pattern) (ha : d122870 p = 1) (hb : d124382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122853 q = 1) (hb : d124377 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122853, d124377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22232 q ha hb
    | true =>
      simp only [d122853, d124377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22191 q ha hb
  have h2 (q : Pattern) (ha : d122854 q = 1) (hb : d124378 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122854, d124378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122854, d124378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122855 q = 1) (hb : d124379 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122855, d124379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122855, d124379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122859 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122860 q = 1) (hb : d124380 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122860, d124380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122860, d124380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122862 q = 1) (hb : d124191 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122862, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22191 q ha hb
    | true =>
      simp only [d122862, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22233 q ha hb
  have h7 (q : Pattern) (ha : d122863 q = 1) (hb : d124192 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122863, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122863, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122864 q = 1) (hb : d124193 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122864, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122864, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122867 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122868 q = 1) (hb : d124194 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122868, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122868, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122869 q = 1) (hb : d124381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122869, d124381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122869, d124381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122870 q = 1) (hb : d124382 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122870, d124382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122870, d124382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro22235 (p : Pattern) (ha : d122875 p = 1) (hb : d124390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122862 q = 1) (hb : d124191 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122862, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22191 q ha hb
    | true =>
      simp only [d122862, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22233 q ha hb
  have h2 (q : Pattern) (ha : d122863 q = 1) (hb : d124192 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122863, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122863, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122864 q = 1) (hb : d124193 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122864, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122864, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122867 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122868 q = 1) (hb : d124194 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122868, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122868, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122865 q = 1) (hb : d124385 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122865, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22233 q ha hb
    | true =>
      simp only [d122865, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h7 (q : Pattern) (ha : d122866 q = 1) (hb : d124386 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122866, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122866, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122867 q = 1) (hb : d124387 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122867, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122867, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122873 q = 1) (hb : d124388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122873, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122873, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122874 q = 1) (hb : d124389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122874, d124389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122874, d124389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122875 q = 1) (hb : d124390 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122875, d124390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122875, d124390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22236 (p : Pattern) (ha : d122881 p = 1) (hb : d124396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122871 q = 1) (hb : d124383 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122871, d124383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22234 q ha hb
    | true =>
      simp only [d122871, d124383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122872 q = 1) (hb : d124384 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122872, d124384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122872, d124384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122876 q = 1) (hb : d124391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122876, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22235 q ha hb
    | true =>
      simp only [d122876, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122877 q = 1) (hb : d124392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122877, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122877, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122878 q = 1) (hb : d124393 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122878, d124393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122878, d124393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122879 q = 1) (hb : d124394 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122879, d124394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122879, d124394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122880 q = 1) (hb : d124395 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122880, d124395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122880, d124395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122881 q = 1) (hb : d124396 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122881, d124396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122881, d124396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22237 (p : Pattern) (ha : d122883 p = 1) (hb : d124398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122865 q = 1) (hb : d124385 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122865, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22233 q ha hb
    | true =>
      simp only [d122865, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h2 (q : Pattern) (ha : d122866 q = 1) (hb : d124386 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122866, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122866, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122867 q = 1) (hb : d124387 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122867, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122867, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122873 q = 1) (hb : d124388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122873, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122873, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122882 q = 1) (hb : d124397 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122882, d124397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122882, d124397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122883 q = 1) (hb : d124398 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122883, d124398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122883, d124398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22238 (p : Pattern) (ha : d122889 p = 1) (hb : d124404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122876 q = 1) (hb : d124391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122876, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22235 q ha hb
    | true =>
      simp only [d122876, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122877 q = 1) (hb : d124392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122877, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122877, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122884 q = 1) (hb : d124399 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122884, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22237 q ha hb
    | true =>
      simp only [d122884, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122885 q = 1) (hb : d124400 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122885, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122885, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122886 q = 1) (hb : d124401 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122886, d124401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122886, d124401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122887 q = 1) (hb : d124402 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122887, d124402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122887, d124402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122888 q = 1) (hb : d124403 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122888, d124403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122888, d124403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122889 q = 1) (hb : d124404 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122889, d124404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122889, d124404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22239 (p : Pattern) (ha : d122900 p = 1) (hb : d124410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122876 q = 1) (hb : d124391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122876, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22235 q ha hb
    | true =>
      simp only [d122876, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122877 q = 1) (hb : d124392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122877, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122877, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122897 q = 1) (hb : d124407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122897, d124407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122897, d124407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122898 q = 1) (hb : d124408 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122898, d124408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122898, d124408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122899 q = 1) (hb : d124409 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122899, d124409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122899, d124409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122900 q = 1) (hb : d124410 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122900, d124410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122900, d124410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22240 (p : Pattern) (ha : d122906 p = 1) (hb : d124416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122890 q = 1) (hb : d124405 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122890, d124405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22236 q ha hb
    | true =>
      simp only [d122890, d124405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22238 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122895 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122896 q = 1) (hb : d124406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122896, d124406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122896, d124406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122901 q = 1) (hb : d124411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122901, d124411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22239 q ha hb
    | true =>
      simp only [d122901, d124411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122902 q = 1) (hb : d124412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122902, d124412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122902, d124412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122903 q = 1) (hb : d124413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122903, d124413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122903, d124413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122904 q = 1) (hb : d124414 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122904, d124414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122904, d124414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122905 q = 1) (hb : d124415 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122905, d124415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122905, d124415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122906 q = 1) (hb : d124416 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122906, d124416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122906, d124416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22241 (p : Pattern) (ha : d122894 p = 1) (hb : d124421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122884 q = 1) (hb : d124399 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122884, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22237 q ha hb
    | true =>
      simp only [d122884, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122885 q = 1) (hb : d124400 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122885, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122885, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122891 q = 1) (hb : d124418 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122891, d124418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122891, d124418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122892 q = 1) (hb : d124419 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122892, d124419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122892, d124419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122893 q = 1) (hb : d124420 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122893, d124420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122893, d124420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122894 q = 1) (hb : d124421 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122894, d124421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122894, d124421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22242 (p : Pattern) (ha : d122913 p = 1) (hb : d124427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122908 q = 1) (hb : d124422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122908, d124422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22241 q ha hb
    | true =>
      simp only [d122908, d124422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122909 q = 1) (hb : d124423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122909, d124423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122909, d124423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122910 q = 1) (hb : d124424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122910, d124424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122910, d124424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122911 q = 1) (hb : d124425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122911, d124425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122911, d124425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122912 q = 1) (hb : d124426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122912, d124426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122912, d124426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122913 q = 1) (hb : d124427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122913, d124427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122913, d124427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22243 (p : Pattern) (ha : d122919 p = 1) (hb : d124433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122735 q = 1) (hb : d124273 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122735, d124273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122735, d124273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22208 q ha hb
  have h2 (q : Pattern) (ha : d122736 q = 1) (hb : d124274 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122736, d124274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122736, d124274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122745 q = 1) (hb : d124283 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122745, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22208 q ha hb
    | true =>
      simp only [d122745, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22211 q ha hb
  have h4 (q : Pattern) (ha : d122746 q = 1) (hb : d124284 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122746, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122746, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122747 q = 1) (hb : d124285 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122747, d124285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122747, d124285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122819 q = 1) (hb : d124349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122819, d124349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22220 q ha hb
    | true =>
      simp only [d122819, d124349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22227 q ha hb
  have h7 (q : Pattern) (ha : d122832 q = 1) (hb : d124362 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122832, d124362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22228 q ha hb
    | true =>
      simp only [d122832, d124362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22229 q ha hb
  have h8 (q : Pattern) (ha : d122833 q = 1) (hb : d124363 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122833, d124363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122833, d124363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122834 q = 1) (hb : d124364 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122834, d124364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122834, d124364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122835 q = 1) (hb : d124365 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122835, d124365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122835, d124365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122839 q = 1) (hb : d124369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122839, d124369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122839, d124369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22230 q ha hb
  have h12 (q : Pattern) (ha : d122841 q = 1) (hb : d124371 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122841, d124371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122841, d124371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22231 q ha hb
  have h13 (q : Pattern) (ha : d122842 q = 1) (hb : d124372 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122842, d124372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122842, d124372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122843 q = 1) (hb : d124373 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122843, d124373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122843, d124373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122844 q = 1) (hb : d124374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122844, d124374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d122844, d124374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122845 q = 1) (hb : d124375 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122845, d124375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122845, d124375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122907 q = 1) (hb : d124417 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122907, d124417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122907, d124417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22240 q ha hb
  have h18 (q : Pattern) (ha : d122914 q = 1) (hb : d124428 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122914, d124428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122914, d124428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22242 q ha hb
  have h19 (q : Pattern) (ha : d122915 q = 1) (hb : d124429 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122915, d124429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122915, d124429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d122916 q = 1) (hb : d124430 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122916, d124430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122916, d124430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122917 q = 1) (hb : d124431 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122917, d124431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d122917, d124431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122918 q = 1) (hb : d124432 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122918, d124432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d122918, d124432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122919 q = 1) (hb : d124433 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122919, d124433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122919, d124433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro22244 (p : Pattern) (ha : d122925 p = 1) (hb : d124439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122920 q = 1) (hb : d124434 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122920, d124434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122920, d124434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22243 q ha hb
  have h2 (q : Pattern) (ha : d122921 q = 1) (hb : d124435 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122921, d124435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122921, d124435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122922 q = 1) (hb : d124436 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122922, d124436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122922, d124436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122923 q = 1) (hb : d124437 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122923, d124437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122923, d124437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122924 q = 1) (hb : d124438 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122924, d124438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122924, d124438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122925 q = 1) (hb : d124439 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122925, d124439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122925, d124439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22245 (p : Pattern) (ha : d12961 p = 1) (hb : d122949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1123 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122943 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12961 q = 1) (hb : d122949 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12961, d122949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12961, d122949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro22246 (p : Pattern) (ha : d122932 p = 1) (hb : d124442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1102 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14757 q = 1) (hb : d122928 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14757, d122928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14757, d122928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122931 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122932 q = 1) (hb : d124442 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122932, d124442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d122932, d124442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro22247 (p : Pattern) (ha : d122937 p = 1) (hb : d124443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14762 q = 1) (hb : d122933 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14762, d122933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14762, d122933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122936 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122937 q = 1) (hb : d124443 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122937, d124443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d122937, d124443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro22248 (p : Pattern) (ha : d122955 p = 1) (hb : d124453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122938 q = 1) (hb : d124444 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122938, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22246 q ha hb
    | true =>
      simp only [d122938, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22247 q ha hb
  have h2 (q : Pattern) (ha : d122939 q = 1) (hb : d124445 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122939, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122939, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122940 q = 1) (hb : d124446 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122940, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122940, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122947 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122948 q = 1) (hb : d124447 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122948, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122948, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122950 q = 1) (hb : d124448 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122950, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22247 q ha hb
    | true =>
      simp only [d122950, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22245 q hb ha
  have h7 (q : Pattern) (ha : d122951 q = 1) (hb : d124449 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122951, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122951, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122952 q = 1) (hb : d124450 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122952, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122952, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122953 q = 1) (hb : d124451 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122953, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122953, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122954 q = 1) (hb : d124452 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122954, d124452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122954, d124452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122955 q = 1) (hb : d124453 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122955, d124453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122955, d124453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22249 (p : Pattern) (ha : d122959 p = 1) (hb : d124457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122950 q = 1) (hb : d124448 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122950, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22247 q ha hb
    | true =>
      simp only [d122950, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22245 q hb ha
  have h2 (q : Pattern) (ha : d122951 q = 1) (hb : d124449 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122951, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122951, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122952 q = 1) (hb : d124450 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122952, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122952, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122953 q = 1) (hb : d124451 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122953, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122953, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122958 q = 1) (hb : d124456 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122958, d124456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122958, d124456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122959 q = 1) (hb : d124457 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122959, d124457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122959, d124457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
end NetHack.Soko22Hazard87
