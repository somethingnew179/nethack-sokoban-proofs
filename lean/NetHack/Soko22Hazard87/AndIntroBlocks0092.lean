import NetHack.Soko22Hazard87.AndIntroBlocks0091
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro23000 (p : Pattern) (ha : d94555 p = 1) (hb : d125748 p = 1) : d126023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d125748 q = 1) : d125891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22578 q ha hb
    | true =>
      simp only [d8378, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d125748 q = 1) : d125892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d125748 q = 1) : d11032 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d11032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22589 q ha hb
    | true =>
      simp only [d684, d11032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d125748 q = 1) : d11033 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d11033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d11033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94552 q = 1) (hb : d125748 q = 1) : d126020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94552, d126020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94552, d126020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94553 q = 1) (hb : d125748 q = 1) : d126021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94553, d126021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94553, d126021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94554 q = 1) (hb : d125748 q = 1) : d126022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94554, d126022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94554, d126022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94555 q = 1) (hb : d125748 q = 1) : d126023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94555, d126023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94555, d126023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23001 (p : Pattern) (ha : d94561 p = 1) (hb : d125748 p = 1) : d126692 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94556 q = 1) (hb : d125748 q = 1) : d126687 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94556, d126687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23000 q ha hb
    | true =>
      simp only [d94556, d126687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22590 q ha hb
  have h2 (q : Pattern) (ha : d94557 q = 1) (hb : d125748 q = 1) : d126688 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94557, d126688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94557, d126688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94558 q = 1) (hb : d125748 q = 1) : d126689 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94558, d126689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94558, d126689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94559 q = 1) (hb : d125748 q = 1) : d126690 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94559, d126690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94559, d126690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94560 q = 1) (hb : d125748 q = 1) : d126691 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94560, d126691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94560, d126691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94561 q = 1) (hb : d125748 q = 1) : d126692 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94561, d126692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94561, d126692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23002 (p : Pattern) (ha : d94567 p = 1) (hb : d125748 p = 1) : d126698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8436 q = 1) (hb : d125748 q = 1) : d125940 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, d125940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22593 q ha hb
    | true =>
      simp only [d8436, d125940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22595 q ha hb
  have h2 (q : Pattern) (ha : d8437 q = 1) (hb : d125748 q = 1) : d125941 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, d125941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8437, d125941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94544 q = 1) (hb : d125748 q = 1) : d126679 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94544, d126679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94544, d126679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94545 q = 1) (hb : d125748 q = 1) : d126680 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94545, d126680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94545, d126680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94547 q = 1) (hb : d125748 q = 1) : d126682 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94547, d126682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94547, d126682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22999 q ha hb
  have h6 (q : Pattern) (ha : d94548 q = 1) (hb : d125748 q = 1) : d126683 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94548, d126683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94548, d126683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94549 q = 1) (hb : d125748 q = 1) : d126684 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94549, d126684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94549, d126684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94550 q = 1) (hb : d125748 q = 1) : d126685 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94550, d126685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94550, d126685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94551 q = 1) (hb : d125748 q = 1) : d126686 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94551, d126686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94551, d126686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94562 q = 1) (hb : d125748 q = 1) : d126693 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94562, d126693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94562, d126693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23001 q ha hb
  have h11 (q : Pattern) (ha : d94563 q = 1) (hb : d125748 q = 1) : d126694 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94563, d126694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94563, d126694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94564 q = 1) (hb : d125748 q = 1) : d126695 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94564, d126695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94564, d126695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94565 q = 1) (hb : d125748 q = 1) : d126696 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94565, d126696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94565, d126696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94566 q = 1) (hb : d125748 q = 1) : d126697 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94566, d126697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94566, d126697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94567 q = 1) (hb : d125748 q = 1) : d126698 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94567, d126698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94567, d126698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23003 (p : Pattern) (ha : d94573 p = 1) (hb : d125748 p = 1) : d126704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94568 q = 1) (hb : d125748 q = 1) : d126699 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94568, d126699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94568, d126699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23002 q ha hb
  have h2 (q : Pattern) (ha : d94569 q = 1) (hb : d125748 q = 1) : d126700 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94569, d126700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94569, d126700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94570 q = 1) (hb : d125748 q = 1) : d126701 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94570, d126701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94570, d126701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94571 q = 1) (hb : d125748 q = 1) : d126702 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94571, d126702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94571, d126702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94572 q = 1) (hb : d125748 q = 1) : d126703 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94572, d126703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94572, d126703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94573 q = 1) (hb : d125748 q = 1) : d126704 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94573, d126704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94573, d126704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23004 (p : Pattern) (ha : d94577 p = 1) (hb : d125748 p = 1) : d126708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8592 q = 1) (hb : d125748 q = 1) : d126067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, d126067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22635 q ha hb
    | true =>
      simp only [d8592, d126067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22626 q ha hb
  have h2 (q : Pattern) (ha : d8593 q = 1) (hb : d125748 q = 1) : d126068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8593, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8594 q = 1) (hb : d125748 q = 1) : d126069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8594, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8595 q = 1) (hb : d125748 q = 1) : d126070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8596 q = 1) (hb : d125748 q = 1) : d126071 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94577 q = 1) (hb : d125748 q = 1) : d126708 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94577, d126708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94577, d126708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23005 (p : Pattern) (ha : d94586 p = 1) (hb : d125748 p = 1) : d126161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8716 q = 1) (hb : d125748 q = 1) : d126152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8716, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22661 q ha hb
    | true =>
      simp only [d8716, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d125748 q = 1) : d126153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d125748 q = 1) : d11290 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22629 q ha hb
    | true =>
      simp only [d1006, d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d125748 q = 1) : d11291 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94583 q = 1) (hb : d125748 q = 1) : d126158 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94583, d126158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94583, d126158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94584 q = 1) (hb : d125748 q = 1) : d126159 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94584, d126159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94584, d126159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94585 q = 1) (hb : d125748 q = 1) : d126160 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94585, d126160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94585, d126160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94586 q = 1) (hb : d125748 q = 1) : d126161 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94586, d126161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94586, d126161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23006 (p : Pattern) (ha : d94592 p = 1) (hb : d125748 p = 1) : d126719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94587 q = 1) (hb : d125748 q = 1) : d126714 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94587, d126714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23005 q ha hb
    | true =>
      simp only [d94587, d126714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22630 q ha hb
  have h2 (q : Pattern) (ha : d94588 q = 1) (hb : d125748 q = 1) : d126715 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94588, d126715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94588, d126715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94589 q = 1) (hb : d125748 q = 1) : d126716 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94589, d126716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94589, d126716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94590 q = 1) (hb : d125748 q = 1) : d126717 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94590, d126717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94590, d126717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94591 q = 1) (hb : d125748 q = 1) : d126718 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94591, d126718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94591, d126718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94592 q = 1) (hb : d125748 q = 1) : d126719 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94592, d126719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94592, d126719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23007 (p : Pattern) (ha : d94598 p = 1) (hb : d125748 p = 1) : d126725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8598 q = 1) (hb : d125748 q = 1) : d126073 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, d126073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22634 q ha hb
    | true =>
      simp only [d8598, d126073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22636 q ha hb
  have h2 (q : Pattern) (ha : d8599 q = 1) (hb : d125748 q = 1) : d126074 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, d126074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8599, d126074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94575 q = 1) (hb : d125748 q = 1) : d126706 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94575, d126706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94575, d126706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94576 q = 1) (hb : d125748 q = 1) : d126707 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94576, d126707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94576, d126707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94578 q = 1) (hb : d125748 q = 1) : d126709 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94578, d126709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94578, d126709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23004 q ha hb
  have h6 (q : Pattern) (ha : d94579 q = 1) (hb : d125748 q = 1) : d126710 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94579, d126710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94579, d126710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94580 q = 1) (hb : d125748 q = 1) : d126711 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94580, d126711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94580, d126711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94581 q = 1) (hb : d125748 q = 1) : d126712 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94581, d126712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94581, d126712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94582 q = 1) (hb : d125748 q = 1) : d126713 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94582, d126713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94582, d126713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94593 q = 1) (hb : d125748 q = 1) : d126720 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94593, d126720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94593, d126720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23006 q ha hb
  have h11 (q : Pattern) (ha : d94594 q = 1) (hb : d125748 q = 1) : d126721 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94594, d126721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94594, d126721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94595 q = 1) (hb : d125748 q = 1) : d126722 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94595, d126722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94595, d126722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94596 q = 1) (hb : d125748 q = 1) : d126723 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94596, d126723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94596, d126723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94597 q = 1) (hb : d125748 q = 1) : d126724 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94597, d126724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94597, d126724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94598 q = 1) (hb : d125748 q = 1) : d126725 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94598, d126725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94598, d126725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23008 (p : Pattern) (ha : d94604 p = 1) (hb : d125748 p = 1) : d126731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94599 q = 1) (hb : d125748 q = 1) : d126726 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94599, d126726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94599, d126726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23007 q ha hb
  have h2 (q : Pattern) (ha : d94600 q = 1) (hb : d125748 q = 1) : d126727 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94600, d126727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94600, d126727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94601 q = 1) (hb : d125748 q = 1) : d126728 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94601, d126728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94601, d126728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94602 q = 1) (hb : d125748 q = 1) : d126729 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94602, d126729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94602, d126729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94603 q = 1) (hb : d125748 q = 1) : d126730 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94603, d126730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94603, d126730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94604 q = 1) (hb : d125748 q = 1) : d126731 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94604, d126731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94604, d126731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23009 (p : Pattern) (ha : d94609 p = 1) (hb : d125748 p = 1) : d126736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8759 q = 1) (hb : d125748 q = 1) : d126206 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, d126206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22677 q ha hb
    | true =>
      simp only [d8759, d126206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22668 q ha hb
  have h2 (q : Pattern) (ha : d8760 q = 1) (hb : d125748 q = 1) : d126207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8760, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8761 q = 1) (hb : d125748 q = 1) : d126208 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8761, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8762 q = 1) (hb : d125748 q = 1) : d126209 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8763 q = 1) (hb : d125748 q = 1) : d126210 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94609 q = 1) (hb : d125748 q = 1) : d126736 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94609, d126736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94609, d126736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23010 (p : Pattern) (ha : d94618 p = 1) (hb : d125748 p = 1) : d126300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8883 q = 1) (hb : d125748 q = 1) : d126291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8883, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22703 q ha hb
    | true =>
      simp only [d8883, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d125748 q = 1) : d126292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d125748 q = 1) : d11560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22671 q ha hb
    | true =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d125748 q = 1) : d11561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94615 q = 1) (hb : d125748 q = 1) : d126297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94615, d126297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94615, d126297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94616 q = 1) (hb : d125748 q = 1) : d126298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94616, d126298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94616, d126298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94617 q = 1) (hb : d125748 q = 1) : d126299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94617, d126299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94617, d126299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94618 q = 1) (hb : d125748 q = 1) : d126300 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94618, d126300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94618, d126300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23011 (p : Pattern) (ha : d94624 p = 1) (hb : d125748 p = 1) : d126747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94619 q = 1) (hb : d125748 q = 1) : d126742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94619, d126742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23010 q ha hb
    | true =>
      simp only [d94619, d126742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22672 q ha hb
  have h2 (q : Pattern) (ha : d94620 q = 1) (hb : d125748 q = 1) : d126743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94620, d126743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94620, d126743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94621 q = 1) (hb : d125748 q = 1) : d126744 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94621, d126744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94621, d126744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94622 q = 1) (hb : d125748 q = 1) : d126745 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94622, d126745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94622, d126745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94623 q = 1) (hb : d125748 q = 1) : d126746 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94623, d126746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94623, d126746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94624 q = 1) (hb : d125748 q = 1) : d126747 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94624, d126747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94624, d126747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23012 (p : Pattern) (ha : d94630 p = 1) (hb : d125748 p = 1) : d126753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8765 q = 1) (hb : d125748 q = 1) : d126212 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, d126212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22676 q ha hb
    | true =>
      simp only [d8765, d126212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22678 q ha hb
  have h2 (q : Pattern) (ha : d8766 q = 1) (hb : d125748 q = 1) : d126213 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, d126213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8766, d126213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94607 q = 1) (hb : d125748 q = 1) : d126734 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94607, d126734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94607, d126734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94608 q = 1) (hb : d125748 q = 1) : d126735 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94608, d126735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94608, d126735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94610 q = 1) (hb : d125748 q = 1) : d126737 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94610, d126737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94610, d126737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23009 q ha hb
  have h6 (q : Pattern) (ha : d94611 q = 1) (hb : d125748 q = 1) : d126738 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94611, d126738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94611, d126738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94612 q = 1) (hb : d125748 q = 1) : d126739 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94612, d126739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94612, d126739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94613 q = 1) (hb : d125748 q = 1) : d126740 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94613, d126740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94613, d126740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94614 q = 1) (hb : d125748 q = 1) : d126741 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94614, d126741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94614, d126741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94625 q = 1) (hb : d125748 q = 1) : d126748 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94625, d126748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94625, d126748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23011 q ha hb
  have h11 (q : Pattern) (ha : d94626 q = 1) (hb : d125748 q = 1) : d126749 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94626, d126749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94626, d126749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94627 q = 1) (hb : d125748 q = 1) : d126750 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94627, d126750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94627, d126750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94628 q = 1) (hb : d125748 q = 1) : d126751 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94628, d126751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94628, d126751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94629 q = 1) (hb : d125748 q = 1) : d126752 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94629, d126752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94629, d126752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94630 q = 1) (hb : d125748 q = 1) : d126753 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94630, d126753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94630, d126753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23013 (p : Pattern) (ha : d94636 p = 1) (hb : d125748 p = 1) : d126759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94631 q = 1) (hb : d125748 q = 1) : d126754 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94631, d126754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94631, d126754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23012 q ha hb
  have h2 (q : Pattern) (ha : d94632 q = 1) (hb : d125748 q = 1) : d126755 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94632, d126755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94632, d126755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94633 q = 1) (hb : d125748 q = 1) : d126756 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94633, d126756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94633, d126756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94634 q = 1) (hb : d125748 q = 1) : d126757 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94634, d126757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94634, d126757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94635 q = 1) (hb : d125748 q = 1) : d126758 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94635, d126758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94635, d126758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94636 q = 1) (hb : d125748 q = 1) : d126759 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94636, d126759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94636, d126759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23014 (p : Pattern) (ha : d94642 p = 1) (hb : d125748 p = 1) : d126765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8927 q = 1) (hb : d125748 q = 1) : d126346 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, d126346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22719 q ha hb
    | true =>
      simp only [d8927, d126346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22710 q ha hb
  have h2 (q : Pattern) (ha : d8928 q = 1) (hb : d125748 q = 1) : d126347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8928, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8929 q = 1) (hb : d125748 q = 1) : d126348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8929, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8930 q = 1) (hb : d125748 q = 1) : d126349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8931 q = 1) (hb : d125748 q = 1) : d126350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94642 q = 1) (hb : d125748 q = 1) : d126765 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94642, d126765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94642, d126765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23015 (p : Pattern) (ha : d94651 p = 1) (hb : d125748 p = 1) : d126440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9051 q = 1) (hb : d125748 q = 1) : d126431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9051, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22745 q ha hb
    | true =>
      simp only [d9051, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d125748 q = 1) : d126432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d125748 q = 1) : d11831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22713 q ha hb
    | true =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d125748 q = 1) : d11832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94648 q = 1) (hb : d125748 q = 1) : d126437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94648, d126437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94648, d126437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94649 q = 1) (hb : d125748 q = 1) : d126438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94649, d126438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94649, d126438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94650 q = 1) (hb : d125748 q = 1) : d126439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94650, d126439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94650, d126439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94651 q = 1) (hb : d125748 q = 1) : d126440 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94651, d126440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94651, d126440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23016 (p : Pattern) (ha : d94657 p = 1) (hb : d125748 p = 1) : d126776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94652 q = 1) (hb : d125748 q = 1) : d126771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94652, d126771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23015 q ha hb
    | true =>
      simp only [d94652, d126771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22714 q ha hb
  have h2 (q : Pattern) (ha : d94653 q = 1) (hb : d125748 q = 1) : d126772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94653, d126772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94653, d126772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94654 q = 1) (hb : d125748 q = 1) : d126773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94654, d126773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94654, d126773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94655 q = 1) (hb : d125748 q = 1) : d126774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94655, d126774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94655, d126774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94656 q = 1) (hb : d125748 q = 1) : d126775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94656, d126775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94656, d126775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94657 q = 1) (hb : d125748 q = 1) : d126776 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94657, d126776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94657, d126776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23017 (p : Pattern) (ha : d94663 p = 1) (hb : d125748 p = 1) : d126782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8933 q = 1) (hb : d125748 q = 1) : d126352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, d126352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22718 q ha hb
    | true =>
      simp only [d8933, d126352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22720 q ha hb
  have h2 (q : Pattern) (ha : d8934 q = 1) (hb : d125748 q = 1) : d126353 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, d126353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8934, d126353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94640 q = 1) (hb : d125748 q = 1) : d126763 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94640, d126763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94640, d126763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94641 q = 1) (hb : d125748 q = 1) : d126764 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94641, d126764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94641, d126764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94643 q = 1) (hb : d125748 q = 1) : d126766 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94643, d126766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94643, d126766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23014 q ha hb
  have h6 (q : Pattern) (ha : d94644 q = 1) (hb : d125748 q = 1) : d126767 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94644, d126767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94644, d126767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94645 q = 1) (hb : d125748 q = 1) : d126768 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94645, d126768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94645, d126768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94646 q = 1) (hb : d125748 q = 1) : d126769 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94646, d126769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94646, d126769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94647 q = 1) (hb : d125748 q = 1) : d126770 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94647, d126770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94647, d126770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94658 q = 1) (hb : d125748 q = 1) : d126777 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94658, d126777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94658, d126777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23016 q ha hb
  have h11 (q : Pattern) (ha : d94659 q = 1) (hb : d125748 q = 1) : d126778 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94659, d126778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94659, d126778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94660 q = 1) (hb : d125748 q = 1) : d126779 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94660, d126779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94660, d126779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94661 q = 1) (hb : d125748 q = 1) : d126780 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94661, d126780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94661, d126780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94662 q = 1) (hb : d125748 q = 1) : d126781 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94662, d126781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94662, d126781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94663 q = 1) (hb : d125748 q = 1) : d126782 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94663, d126782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94663, d126782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23018 (p : Pattern) (ha : d94669 p = 1) (hb : d125748 p = 1) : d126788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94664 q = 1) (hb : d125748 q = 1) : d126783 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94664, d126783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94664, d126783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23017 q ha hb
  have h2 (q : Pattern) (ha : d94665 q = 1) (hb : d125748 q = 1) : d126784 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94665, d126784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94665, d126784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94666 q = 1) (hb : d125748 q = 1) : d126785 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94666, d126785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94666, d126785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94667 q = 1) (hb : d125748 q = 1) : d126786 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94667, d126786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94667, d126786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94668 q = 1) (hb : d125748 q = 1) : d126787 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94668, d126787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94668, d126787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94669 q = 1) (hb : d125748 q = 1) : d126788 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94669, d126788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94669, d126788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23019 (p : Pattern) (ha : d94676 p = 1) (hb : d125748 p = 1) : d126795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9096 q = 1) (hb : d125748 q = 1) : d126487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, d126487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22761 q ha hb
    | true =>
      simp only [d9096, d126487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22752 q ha hb
  have h2 (q : Pattern) (ha : d9097 q = 1) (hb : d125748 q = 1) : d126488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9097, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9098 q = 1) (hb : d125748 q = 1) : d126489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9098, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9099 q = 1) (hb : d125748 q = 1) : d126490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9100 q = 1) (hb : d125748 q = 1) : d126491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94676 q = 1) (hb : d125748 q = 1) : d126795 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94676, d126795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94676, d126795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23020 (p : Pattern) (ha : d94685 p = 1) (hb : d125748 p = 1) : d126581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9220 q = 1) (hb : d125748 q = 1) : d126572 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9220, d126572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22787 q ha hb
    | true =>
      simp only [d9220, d126572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9221 q = 1) (hb : d125748 q = 1) : d126573 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, d126573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9221, d126573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d125748 q = 1) : d12103 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d12103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22755 q ha hb
    | true =>
      simp only [d2386, d12103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d125748 q = 1) : d12104 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d12104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d12104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94682 q = 1) (hb : d125748 q = 1) : d126578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94682, d126578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94682, d126578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94683 q = 1) (hb : d125748 q = 1) : d126579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94683, d126579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94683, d126579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94684 q = 1) (hb : d125748 q = 1) : d126580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94684, d126580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94684, d126580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94685 q = 1) (hb : d125748 q = 1) : d126581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94685, d126581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94685, d126581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23021 (p : Pattern) (ha : d94691 p = 1) (hb : d125748 p = 1) : d126806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94686 q = 1) (hb : d125748 q = 1) : d126801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94686, d126801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23020 q ha hb
    | true =>
      simp only [d94686, d126801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22756 q ha hb
  have h2 (q : Pattern) (ha : d94687 q = 1) (hb : d125748 q = 1) : d126802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94687, d126802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94687, d126802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94688 q = 1) (hb : d125748 q = 1) : d126803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94688, d126803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94688, d126803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94689 q = 1) (hb : d125748 q = 1) : d126804 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94689, d126804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94689, d126804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94690 q = 1) (hb : d125748 q = 1) : d126805 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94690, d126805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94690, d126805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94691 q = 1) (hb : d125748 q = 1) : d126806 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94691, d126806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94691, d126806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23022 (p : Pattern) (ha : d94697 p = 1) (hb : d125748 p = 1) : d126812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9102 q = 1) (hb : d125748 q = 1) : d126493 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, d126493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22760 q ha hb
    | true =>
      simp only [d9102, d126493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22762 q ha hb
  have h2 (q : Pattern) (ha : d9103 q = 1) (hb : d125748 q = 1) : d126494 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, d126494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9103, d126494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94674 q = 1) (hb : d125748 q = 1) : d126793 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94674, d126793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94674, d126793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94675 q = 1) (hb : d125748 q = 1) : d126794 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94675, d126794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94675, d126794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94677 q = 1) (hb : d125748 q = 1) : d126796 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94677, d126796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94677, d126796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23019 q ha hb
  have h6 (q : Pattern) (ha : d94678 q = 1) (hb : d125748 q = 1) : d126797 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94678, d126797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94678, d126797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94679 q = 1) (hb : d125748 q = 1) : d126798 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94679, d126798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94679, d126798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94680 q = 1) (hb : d125748 q = 1) : d126799 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94680, d126799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94680, d126799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94681 q = 1) (hb : d125748 q = 1) : d126800 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94681, d126800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94681, d126800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94692 q = 1) (hb : d125748 q = 1) : d126807 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94692, d126807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94692, d126807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23021 q ha hb
  have h11 (q : Pattern) (ha : d94693 q = 1) (hb : d125748 q = 1) : d126808 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94693, d126808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94693, d126808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94694 q = 1) (hb : d125748 q = 1) : d126809 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94694, d126809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94694, d126809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94695 q = 1) (hb : d125748 q = 1) : d126810 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94695, d126810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94695, d126810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94696 q = 1) (hb : d125748 q = 1) : d126811 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94696, d126811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94696, d126811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94697 q = 1) (hb : d125748 q = 1) : d126812 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94697, d126812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94697, d126812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23023 (p : Pattern) (ha : d94703 p = 1) (hb : d125748 p = 1) : d126818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94698 q = 1) (hb : d125748 q = 1) : d126813 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94698, d126813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94698, d126813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23022 q ha hb
  have h2 (q : Pattern) (ha : d94699 q = 1) (hb : d125748 q = 1) : d126814 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94699, d126814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94699, d126814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94700 q = 1) (hb : d125748 q = 1) : d126815 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94700, d126815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94700, d126815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94701 q = 1) (hb : d125748 q = 1) : d126816 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94701, d126816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94701, d126816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94702 q = 1) (hb : d125748 q = 1) : d126817 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94702, d126817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94702, d126817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94703 q = 1) (hb : d125748 q = 1) : d126818 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94703, d126818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94703, d126818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23024 (p : Pattern) (ha : d94709 p = 1) (hb : d125748 p = 1) : d126824 p = 1 := by
  have h0 (q : Pattern) (ha : d94574 q = 1) (hb : d125748 q = 1) : d126705 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94574, d126705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22998 q ha hb
    | true =>
      simp only [d94574, d126705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23003 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94605 q = 1) (hb : d125748 q = 1) : d126732 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94605, d126732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94605, d126732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23008 q ha hb
  have h3 (q : Pattern) (ha : d94606 q = 1) (hb : d125748 q = 1) : d126733 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94606, d126733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94606, d126733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94637 q = 1) (hb : d125748 q = 1) : d126760 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94637, d126760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94637, d126760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23013 q ha hb
  have h5 (q : Pattern) (ha : d94638 q = 1) (hb : d125748 q = 1) : d126761 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94638, d126761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94638, d126761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94639 q = 1) (hb : d125748 q = 1) : d126762 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94639, d126762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94639, d126762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94670 q = 1) (hb : d125748 q = 1) : d126789 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94670, d126789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94670, d126789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23018 q ha hb
  have h8 (q : Pattern) (ha : d94671 q = 1) (hb : d125748 q = 1) : d126790 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94671, d126790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94671, d126790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94672 q = 1) (hb : d125748 q = 1) : d126791 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94672, d126791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94672, d126791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94673 q = 1) (hb : d125748 q = 1) : d126792 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94673, d126792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94673, d126792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94704 q = 1) (hb : d125748 q = 1) : d126819 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94704, d126819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94704, d126819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23023 q ha hb
  have h12 (q : Pattern) (ha : d94705 q = 1) (hb : d125748 q = 1) : d126820 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94705, d126820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94705, d126820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94706 q = 1) (hb : d125748 q = 1) : d126821 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94706, d126821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94706, d126821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94707 q = 1) (hb : d125748 q = 1) : d126822 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94707, d126822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94707, d126822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94708 q = 1) (hb : d125748 q = 1) : d126823 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94708, d126823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94708, d126823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94709 q = 1) (hb : d125748 q = 1) : d126824 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94709, d126824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94709, d126824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro23025 (p : Pattern) (ha : d94715 p = 1) (hb : d125748 p = 1) : d126830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94710 q = 1) (hb : d125748 q = 1) : d126825 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94710, d126825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23024 q ha hb
    | true =>
      simp only [d94710, d126825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94711 q = 1) (hb : d125748 q = 1) : d126826 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94711, d126826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94711, d126826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94712 q = 1) (hb : d125748 q = 1) : d126827 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94712, d126827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94712, d126827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94713 q = 1) (hb : d125748 q = 1) : d126828 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94713, d126828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94713, d126828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94714 q = 1) (hb : d125748 q = 1) : d126829 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94714, d126829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94714, d126829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94715 q = 1) (hb : d125748 q = 1) : d126830 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94715, d126830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94715, d126830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23026 (p : Pattern) (ha : d94721 p = 1) (hb : d125748 p = 1) : d126836 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94716 q = 1) (hb : d125748 q = 1) : d126831 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94716, d126831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23025 q ha hb
    | true =>
      simp only [d94716, d126831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94717 q = 1) (hb : d125748 q = 1) : d126832 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94717, d126832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94717, d126832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94718 q = 1) (hb : d125748 q = 1) : d126833 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94718, d126833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94718, d126833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94719 q = 1) (hb : d125748 q = 1) : d126834 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94719, d126834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94719, d126834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94720 q = 1) (hb : d125748 q = 1) : d126835 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94720, d126835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94720, d126835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94721 q = 1) (hb : d125748 q = 1) : d126836 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94721, d126836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94721, d126836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23027 (p : Pattern) (ha : d94727 p = 1) (hb : d125748 p = 1) : d126842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94722 q = 1) (hb : d125748 q = 1) : d126837 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94722, d126837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23026 q ha hb
    | true =>
      simp only [d94722, d126837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94723 q = 1) (hb : d125748 q = 1) : d126838 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94723, d126838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94723, d126838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94724 q = 1) (hb : d125748 q = 1) : d126839 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94724, d126839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94724, d126839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94725 q = 1) (hb : d125748 q = 1) : d126840 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94725, d126840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94725, d126840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94726 q = 1) (hb : d125748 q = 1) : d126841 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94726, d126841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94726, d126841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94727 q = 1) (hb : d125748 q = 1) : d126842 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94727, d126842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94727, d126842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23028 (p : Pattern) (ha : d94733 p = 1) (hb : d125748 p = 1) : d126848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94728 q = 1) (hb : d125748 q = 1) : d126843 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94728, d126843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23027 q ha hb
    | true =>
      simp only [d94728, d126843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94729 q = 1) (hb : d125748 q = 1) : d126844 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94729, d126844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94729, d126844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94730 q = 1) (hb : d125748 q = 1) : d126845 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94730, d126845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94730, d126845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94731 q = 1) (hb : d125748 q = 1) : d126846 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94731, d126846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94731, d126846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94732 q = 1) (hb : d125748 q = 1) : d126847 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94732, d126847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94732, d126847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94733 q = 1) (hb : d125748 q = 1) : d126848 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94733, d126848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94733, d126848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23029 (p : Pattern) (ha : d94739 p = 1) (hb : d125748 p = 1) : d126854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94734 q = 1) (hb : d125748 q = 1) : d126849 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94734, d126849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23028 q ha hb
    | true =>
      simp only [d94734, d126849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94735 q = 1) (hb : d125748 q = 1) : d126850 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94735, d126850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94735, d126850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94736 q = 1) (hb : d125748 q = 1) : d126851 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94736, d126851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94736, d126851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94737 q = 1) (hb : d125748 q = 1) : d126852 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94737, d126852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94737, d126852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94738 q = 1) (hb : d125748 q = 1) : d126853 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94738, d126853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94738, d126853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94739 q = 1) (hb : d125748 q = 1) : d126854 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94739, d126854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94739, d126854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23030 (p : Pattern) (ha : d94745 p = 1) (hb : d125748 p = 1) : d126860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94740 q = 1) (hb : d125748 q = 1) : d126855 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94740, d126855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23029 q ha hb
    | true =>
      simp only [d94740, d126855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94741 q = 1) (hb : d125748 q = 1) : d126856 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94741, d126856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94741, d126856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94742 q = 1) (hb : d125748 q = 1) : d126857 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94742, d126857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94742, d126857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94743 q = 1) (hb : d125748 q = 1) : d126858 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94743, d126858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94743, d126858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94744 q = 1) (hb : d125748 q = 1) : d126859 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94744, d126859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94744, d126859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94745 q = 1) (hb : d125748 q = 1) : d126860 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94745, d126860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94745, d126860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23031 (p : Pattern) (ha : d94751 p = 1) (hb : d125748 p = 1) : d126866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94746 q = 1) (hb : d125748 q = 1) : d126861 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94746, d126861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23030 q ha hb
    | true =>
      simp only [d94746, d126861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94747 q = 1) (hb : d125748 q = 1) : d126862 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94747, d126862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94747, d126862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94748 q = 1) (hb : d125748 q = 1) : d126863 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94748, d126863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94748, d126863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94749 q = 1) (hb : d125748 q = 1) : d126864 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94749, d126864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94749, d126864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94750 q = 1) (hb : d125748 q = 1) : d126865 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94750, d126865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94750, d126865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94751 q = 1) (hb : d125748 q = 1) : d126866 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94751, d126866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94751, d126866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23032 (p : Pattern) (ha : d107602 p = 1) (hb : d125811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107578 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107591 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d107498 q = 1) (hb : d125757 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22801 q ha hb
    | true =>
      simp only [d107498, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d107592 q = 1) (hb : d125807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d107592, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d107598 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107599 q = 1) (hb : d125808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107599, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107600 q = 1) (hb : d125809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107600, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107601 q = 1) (hb : d125810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107601, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107602 q = 1) (hb : d125811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107602, d125811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107602, d125811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro23033 (p : Pattern) (ha : d107621 p = 1) (hb : d125818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107591 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107498 q = 1) (hb : d125757 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22801 q ha hb
    | true =>
      simp only [d107498, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d107592 q = 1) (hb : d125807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107592, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d107598 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d107599 q = 1) (hb : d125808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107599, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107600 q = 1) (hb : d125809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107600, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107601 q = 1) (hb : d125810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107601, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107607 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107611 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d107613 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d107505 q = 1) (hb : d125764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22803 q ha hb
    | true =>
      simp only [d107505, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d107614 q = 1) (hb : d125814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d107614, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107617 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107618 q = 1) (hb : d125815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107618, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107619 q = 1) (hb : d125816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107619, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d107619, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107620 q = 1) (hb : d125817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107620, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d107620, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107621 q = 1) (hb : d125818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107621, d125818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107621, d125818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro23034 (p : Pattern) (ha : d107630 p = 1) (hb : d126656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107613 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107505 q = 1) (hb : d125764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22803 q ha hb
    | true =>
      simp only [d107505, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d107614 q = 1) (hb : d125814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107614, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107617 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107618 q = 1) (hb : d125815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107618, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107628 q = 1) (hb : d125816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107628, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107628, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107629 q = 1) (hb : d125817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107629, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107629, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107630 q = 1) (hb : d126656 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107630, d126656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107630, d126656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23035 (p : Pattern) (ha : d107659 p = 1) (hb : d126666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107535 q = 1) (hb : d125790 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107535, d125790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22807 q ha hb
    | true =>
      simp only [d107535, d125790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d107649 q = 1) (hb : d126662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107649, d126662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107649, d126662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107655 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107656 q = 1) (hb : d126663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107656, d126663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107656, d126663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107657 q = 1) (hb : d126664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107657, d126664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107657, d126664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107658 q = 1) (hb : d126665 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107658, d126665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107658, d126665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107659 q = 1) (hb : d126666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107659, d126666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107659, d126666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23036 (p : Pattern) (ha : d107665 p = 1) (hb : d126672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107566 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107622 q = 1) (hb : d125819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107622, d125819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23032 q ha hb
    | true =>
      simp only [d107622, d125819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23033 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107624 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107625 q = 1) (hb : d125820 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107625, d125820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107625, d125820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107626 q = 1) (hb : d126654 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107626, d126654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107626, d126654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107627 q = 1) (hb : d126655 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107627, d126655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107627, d126655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107631 q = 1) (hb : d126657 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107631, d126657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107631, d126657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23034 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107632 q = 1) (hb : d126658 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107632, d126658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107632, d126658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107633 q = 1) (hb : d126659 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107633, d126659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107633, d126659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d107634 q = 1) (hb : d126660 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107634, d126660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107634, d126660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d107635 q = 1) (hb : d126661 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107635, d126661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107635, d126661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107660 q = 1) (hb : d126667 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107660, d126667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107660, d126667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23035 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107661 q = 1) (hb : d126668 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107661, d126668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107661, d126668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107662 q = 1) (hb : d126669 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107662, d126669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107662, d126669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d107663 q = 1) (hb : d126670 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107663, d126670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107663, d126670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d107664 q = 1) (hb : d126671 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107664, d126671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107664, d126671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d107665 q = 1) (hb : d126672 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107665, d126672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107665, d126672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23037 (p : Pattern) (ha : d107671 p = 1) (hb : d126678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d107547 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d107547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d107547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16176 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d107548 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d107548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d107548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d107549 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d107549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d107549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d107550 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d107550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d107550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d107551 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d107551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d107551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107666 q = 1) (hb : d126673 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107666, d126673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107666, d126673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23036 q ha hb
  have h8 (q : Pattern) (ha : d107667 q = 1) (hb : d126674 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107667, d126674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107667, d126674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107668 q = 1) (hb : d126675 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107668, d126675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107668, d126675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107669 q = 1) (hb : d126676 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107669, d126676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107669, d126676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107670 q = 1) (hb : d126677 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107670, d126677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107670, d126677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107671 q = 1) (hb : d126678 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107671, d126678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d107671, d126678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro23038 (p : Pattern) (ha : d107748 p = 1) (hb : d125930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107715 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107724 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107737 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d107689 q = 1) (hb : d125925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22832 q ha hb
    | true =>
      simp only [d107689, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15937 q hb ha
  have h5 (q : Pattern) (ha : d107738 q = 1) (hb : d125926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d107738, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d107744 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107745 q = 1) (hb : d125927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107745, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107746 q = 1) (hb : d125928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107746, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107747 q = 1) (hb : d125929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107747, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107748 q = 1) (hb : d125930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107748, d125930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107748, d125930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro23039 (p : Pattern) (ha : d107769 p = 1) (hb : d125939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107715 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107737 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107689 q = 1) (hb : d125925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22832 q ha hb
    | true =>
      simp only [d107689, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15937 q hb ha
  have h4 (q : Pattern) (ha : d107738 q = 1) (hb : d125926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107738, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d107744 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d107745 q = 1) (hb : d125927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107745, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107746 q = 1) (hb : d125928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107746, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107747 q = 1) (hb : d125929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107747, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107754 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107759 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d107761 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d107699 q = 1) (hb : d125934 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107699, d125934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22834 q ha hb
    | true =>
      simp only [d107699, d125934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15940 q hb ha
  have h13 (q : Pattern) (ha : d107762 q = 1) (hb : d125935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d107762, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107765 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107766 q = 1) (hb : d125936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107766, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107767 q = 1) (hb : d125937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107767, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d107767, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107768 q = 1) (hb : d125938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107768, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d107768, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107769 q = 1) (hb : d125939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107769, d125939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107769, d125939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro23040 (p : Pattern) (ha : d107789 p = 1) (hb : d126681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107699 q = 1) (hb : d125934 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107699, d125934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22834 q ha hb
    | true =>
      simp only [d107699, d125934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15940 q hb ha
  have h3 (q : Pattern) (ha : d107762 q = 1) (hb : d125935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107762, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107765 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107766 q = 1) (hb : d125936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107766, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107787 q = 1) (hb : d125937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107787, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107787, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107788 q = 1) (hb : d125938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107788, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107788, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107789 q = 1) (hb : d126681 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107789, d126681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107789, d126681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23041 (p : Pattern) (ha : d107838 p = 1) (hb : d126692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107822 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107827 q = 1) (hb : d126687 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107827, d126687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22854 q ha hb
    | true =>
      simp only [d107827, d126687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15946 q hb ha
  have h3 (q : Pattern) (ha : d107828 q = 1) (hb : d126688 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107828, d126688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107828, d126688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107834 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107835 q = 1) (hb : d126689 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107835, d126689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107835, d126689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107836 q = 1) (hb : d126690 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107836, d126690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107836, d126690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107837 q = 1) (hb : d126691 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107837, d126691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107837, d126691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107838 q = 1) (hb : d126692 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107838, d126692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107838, d126692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23042 (p : Pattern) (ha : d107851 p = 1) (hb : d126698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107707 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107770 q = 1) (hb : d125940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107770, d125940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23038 q ha hb
    | true =>
      simp only [d107770, d125940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23039 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107783 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107784 q = 1) (hb : d125941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107784, d125941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107784, d125941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107785 q = 1) (hb : d126679 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107785, d126679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107785, d126679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107786 q = 1) (hb : d126680 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107786, d126680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107786, d126680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107790 q = 1) (hb : d126682 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107790, d126682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107790, d126682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23040 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107792 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107793 q = 1) (hb : d126683 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107793, d126683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107793, d126683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107794 q = 1) (hb : d126684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107794, d126684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107794, d126684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d107795 q = 1) (hb : d126685 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107795, d126685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107795, d126685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d107796 q = 1) (hb : d126686 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107796, d126686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107796, d126686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107839 q = 1) (hb : d126693 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107839, d126693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107839, d126693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23041 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107846 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107847 q = 1) (hb : d126694 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107847, d126694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107847, d126694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107848 q = 1) (hb : d126695 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107848, d126695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107848, d126695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d107849 q = 1) (hb : d126696 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107849, d126696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107849, d126696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d107850 q = 1) (hb : d126697 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107850, d126697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107850, d126697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d107851 q = 1) (hb : d126698 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107851, d126698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107851, d126698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23043 (p : Pattern) (ha : d107857 p = 1) (hb : d126704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107852 q = 1) (hb : d126699 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107852, d126699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107852, d126699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23042 q ha hb
  have h2 (q : Pattern) (ha : d107853 q = 1) (hb : d126700 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107853, d126700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107853, d126700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107854 q = 1) (hb : d126701 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107854, d126701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107854, d126701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107855 q = 1) (hb : d126702 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107855, d126702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107855, d126702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107856 q = 1) (hb : d126703 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107856, d126703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107856, d126703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107857 q = 1) (hb : d126704 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107857, d126704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107857, d126704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23044 (p : Pattern) (ha : d107950 p = 1) (hb : d126063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107918 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107931 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d107883 q = 1) (hb : d126058 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22860 q ha hb
    | true =>
      simp only [d107883, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15975 q hb ha
  have h5 (q : Pattern) (ha : d107932 q = 1) (hb : d126059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d107932, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d107946 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107947 q = 1) (hb : d126060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107947, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107948 q = 1) (hb : d126061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107948, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107949 q = 1) (hb : d126062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107949, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107950 q = 1) (hb : d126063 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107950, d126063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107950, d126063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro23045 (p : Pattern) (ha : d107971 p = 1) (hb : d126072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107909 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107918 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107931 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107883 q = 1) (hb : d126058 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22860 q ha hb
    | true =>
      simp only [d107883, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15975 q hb ha
  have h4 (q : Pattern) (ha : d107932 q = 1) (hb : d126059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107932, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d107946 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d107947 q = 1) (hb : d126060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107947, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107948 q = 1) (hb : d126061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107948, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107949 q = 1) (hb : d126062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107949, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107956 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107961 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d107963 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d107893 q = 1) (hb : d126067 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107893, d126067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22862 q ha hb
    | true =>
      simp only [d107893, d126067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15978 q hb ha
  have h13 (q : Pattern) (ha : d107964 q = 1) (hb : d126068 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d107964, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107967 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107968 q = 1) (hb : d126069 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107968, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107969 q = 1) (hb : d126070 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107969, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d107969, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107970 q = 1) (hb : d126071 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107970, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d107970, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107971 q = 1) (hb : d126072 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107971, d126072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107971, d126072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro23046 (p : Pattern) (ha : d107991 p = 1) (hb : d126708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107963 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107893 q = 1) (hb : d126067 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107893, d126067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22862 q ha hb
    | true =>
      simp only [d107893, d126067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15978 q hb ha
  have h3 (q : Pattern) (ha : d107964 q = 1) (hb : d126068 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107964, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107967 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107968 q = 1) (hb : d126069 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107968, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107989 q = 1) (hb : d126070 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107989, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107989, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107990 q = 1) (hb : d126071 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107990, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107990, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107991 q = 1) (hb : d126708 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107991, d126708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107991, d126708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23047 (p : Pattern) (ha : d108055 p = 1) (hb : d126719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108031 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108036 q = 1) (hb : d126714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108036, d126714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22884 q ha hb
    | true =>
      simp only [d108036, d126714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15984 q hb ha
  have h3 (q : Pattern) (ha : d108037 q = 1) (hb : d126715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108037, d126715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108037, d126715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108051 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108052 q = 1) (hb : d126716 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108052, d126716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108052, d126716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108053 q = 1) (hb : d126717 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108053, d126717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108053, d126717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108054 q = 1) (hb : d126718 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108054, d126718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108054, d126718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108055 q = 1) (hb : d126719 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108055, d126719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108055, d126719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23048 (p : Pattern) (ha : d108068 p = 1) (hb : d126725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107972 q = 1) (hb : d126073 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107972, d126073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23044 q ha hb
    | true =>
      simp only [d107972, d126073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23045 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107986 q = 1) (hb : d126074 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107986, d126074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107986, d126074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107987 q = 1) (hb : d126706 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107987, d126706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107987, d126706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107988 q = 1) (hb : d126707 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107988, d126707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107988, d126707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107992 q = 1) (hb : d126709 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107992, d126709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107992, d126709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23046 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107994 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107995 q = 1) (hb : d126710 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107995, d126710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107995, d126710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107996 q = 1) (hb : d126711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107996, d126711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107996, d126711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d107997 q = 1) (hb : d126712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107997, d126712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107997, d126712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d107998 q = 1) (hb : d126713 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107998, d126713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107998, d126713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108056 q = 1) (hb : d126720 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108056, d126720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108056, d126720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23047 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108063 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108064 q = 1) (hb : d126721 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108064, d126721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108064, d126721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108065 q = 1) (hb : d126722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108065, d126722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108065, d126722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108066 q = 1) (hb : d126723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108066, d126723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108066, d126723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108067 q = 1) (hb : d126724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108067, d126724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108067, d126724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108068 q = 1) (hb : d126725 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108068, d126725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108068, d126725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23049 (p : Pattern) (ha : d108074 p = 1) (hb : d126731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108069 q = 1) (hb : d126726 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108069, d126726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108069, d126726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23048 q ha hb
  have h2 (q : Pattern) (ha : d108070 q = 1) (hb : d126727 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108070, d126727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108070, d126727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108071 q = 1) (hb : d126728 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108071, d126728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108071, d126728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108072 q = 1) (hb : d126729 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108072, d126729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108072, d126729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108073 q = 1) (hb : d126730 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108073, d126730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108073, d126730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108074 q = 1) (hb : d126731 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108074, d126731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108074, d126731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23050 (p : Pattern) (ha : d108168 p = 1) (hb : d126202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108136 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d108149 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108101 q = 1) (hb : d126197 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22892 q ha hb
    | true =>
      simp only [d108101, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16015 q hb ha
  have h5 (q : Pattern) (ha : d108150 q = 1) (hb : d126198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108150, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d108164 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108165 q = 1) (hb : d126199 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108165, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108166 q = 1) (hb : d126200 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108166, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108167 q = 1) (hb : d126201 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108167, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108168 q = 1) (hb : d126202 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108168, d126202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108168, d126202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro23051 (p : Pattern) (ha : d108189 p = 1) (hb : d126211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108136 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108149 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108101 q = 1) (hb : d126197 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22892 q ha hb
    | true =>
      simp only [d108101, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16015 q hb ha
  have h4 (q : Pattern) (ha : d108150 q = 1) (hb : d126198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108150, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d108164 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108165 q = 1) (hb : d126199 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108165, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108166 q = 1) (hb : d126200 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108166, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108167 q = 1) (hb : d126201 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108167, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108174 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d108179 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d108181 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d108111 q = 1) (hb : d126206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108111, d126206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22894 q ha hb
    | true =>
      simp only [d108111, d126206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16018 q hb ha
  have h13 (q : Pattern) (ha : d108182 q = 1) (hb : d126207 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108182, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108185 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108186 q = 1) (hb : d126208 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108186, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108187 q = 1) (hb : d126209 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108187, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108187, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108188 q = 1) (hb : d126210 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108188, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108188, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108189 q = 1) (hb : d126211 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108189, d126211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108189, d126211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro23052 (p : Pattern) (ha : d108209 p = 1) (hb : d126736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108181 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108111 q = 1) (hb : d126206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108111, d126206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22894 q ha hb
    | true =>
      simp only [d108111, d126206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16018 q hb ha
  have h3 (q : Pattern) (ha : d108182 q = 1) (hb : d126207 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108182, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108185 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108186 q = 1) (hb : d126208 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108186, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108207 q = 1) (hb : d126209 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108207, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108207, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108208 q = 1) (hb : d126210 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108208, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108208, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108209 q = 1) (hb : d126736 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108209, d126736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108209, d126736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23053 (p : Pattern) (ha : d108273 p = 1) (hb : d126747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108249 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108254 q = 1) (hb : d126742 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108254, d126742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22916 q ha hb
    | true =>
      simp only [d108254, d126742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16024 q hb ha
  have h3 (q : Pattern) (ha : d108255 q = 1) (hb : d126743 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108255, d126743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108255, d126743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108269 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108270 q = 1) (hb : d126744 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108270, d126744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108270, d126744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108271 q = 1) (hb : d126745 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108271, d126745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108271, d126745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108272 q = 1) (hb : d126746 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108272, d126746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108272, d126746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108273 q = 1) (hb : d126747 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108273, d126747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108273, d126747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23054 (p : Pattern) (ha : d108286 p = 1) (hb : d126753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108119 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108190 q = 1) (hb : d126212 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108190, d126212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23050 q ha hb
    | true =>
      simp only [d108190, d126212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23051 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108203 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108204 q = 1) (hb : d126213 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108204, d126213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108204, d126213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108205 q = 1) (hb : d126734 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108205, d126734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108205, d126734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108206 q = 1) (hb : d126735 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108206, d126735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108206, d126735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108210 q = 1) (hb : d126737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108210, d126737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108210, d126737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23052 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108212 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108213 q = 1) (hb : d126738 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108213, d126738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108213, d126738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108214 q = 1) (hb : d126739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108214, d126739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108214, d126739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d108215 q = 1) (hb : d126740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108215, d126740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108215, d126740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d108216 q = 1) (hb : d126741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108216, d126741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108216, d126741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108274 q = 1) (hb : d126748 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108274, d126748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108274, d126748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23053 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108281 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108282 q = 1) (hb : d126749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108282, d126749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108282, d126749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108283 q = 1) (hb : d126750 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108283, d126750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108283, d126750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108284 q = 1) (hb : d126751 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108284, d126751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108284, d126751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108285 q = 1) (hb : d126752 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108285, d126752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108285, d126752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108286 q = 1) (hb : d126753 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108286, d126753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108286, d126753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23055 (p : Pattern) (ha : d108292 p = 1) (hb : d126759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108287 q = 1) (hb : d126754 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108287, d126754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108287, d126754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23054 q ha hb
  have h2 (q : Pattern) (ha : d108288 q = 1) (hb : d126755 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108288, d126755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108288, d126755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108289 q = 1) (hb : d126756 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108289, d126756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108289, d126756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108290 q = 1) (hb : d126757 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108290, d126757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108290, d126757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108291 q = 1) (hb : d126758 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108291, d126758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108291, d126758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108292 q = 1) (hb : d126759 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108292, d126759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108292, d126759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23056 (p : Pattern) (ha : d108387 p = 1) (hb : d126342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108346 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108355 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d108368 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108320 q = 1) (hb : d126337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22924 q ha hb
    | true =>
      simp only [d108320, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16055 q hb ha
  have h5 (q : Pattern) (ha : d108369 q = 1) (hb : d126338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108369, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d108383 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108384 q = 1) (hb : d126339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108384, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108385 q = 1) (hb : d126340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108385, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108386 q = 1) (hb : d126341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108386, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108387 q = 1) (hb : d126342 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108387, d126342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108387, d126342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro23057 (p : Pattern) (ha : d108408 p = 1) (hb : d126351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108346 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108368 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108320 q = 1) (hb : d126337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22924 q ha hb
    | true =>
      simp only [d108320, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16055 q hb ha
  have h4 (q : Pattern) (ha : d108369 q = 1) (hb : d126338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108369, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d108383 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108384 q = 1) (hb : d126339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108384, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108385 q = 1) (hb : d126340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108385, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108386 q = 1) (hb : d126341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108386, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108393 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d108398 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d108400 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d108330 q = 1) (hb : d126346 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108330, d126346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22926 q ha hb
    | true =>
      simp only [d108330, d126346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16058 q hb ha
  have h13 (q : Pattern) (ha : d108401 q = 1) (hb : d126347 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108401, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108404 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108405 q = 1) (hb : d126348 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108405, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108406 q = 1) (hb : d126349 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108406, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108406, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108407 q = 1) (hb : d126350 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108407, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108407, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108408 q = 1) (hb : d126351 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108408, d126351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108408, d126351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro23058 (p : Pattern) (ha : d108428 p = 1) (hb : d126765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108400 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108330 q = 1) (hb : d126346 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108330, d126346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22926 q ha hb
    | true =>
      simp only [d108330, d126346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16058 q hb ha
  have h3 (q : Pattern) (ha : d108401 q = 1) (hb : d126347 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108401, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108404 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108405 q = 1) (hb : d126348 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108405, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108426 q = 1) (hb : d126349 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108426, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108426, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108427 q = 1) (hb : d126350 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108427, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108427, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108428 q = 1) (hb : d126765 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108428, d126765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108428, d126765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23059 (p : Pattern) (ha : d108492 p = 1) (hb : d126776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108473 q = 1) (hb : d126771 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108473, d126771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22948 q ha hb
    | true =>
      simp only [d108473, d126771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16064 q hb ha
  have h3 (q : Pattern) (ha : d108474 q = 1) (hb : d126772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108474, d126772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108474, d126772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108488 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108489 q = 1) (hb : d126773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108489, d126773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108489, d126773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108490 q = 1) (hb : d126774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108490, d126774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108490, d126774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108491 q = 1) (hb : d126775 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108491, d126775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108491, d126775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108492 q = 1) (hb : d126776 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108492, d126776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108492, d126776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23060 (p : Pattern) (ha : d108505 p = 1) (hb : d126782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108338 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108409 q = 1) (hb : d126352 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108409, d126352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23056 q ha hb
    | true =>
      simp only [d108409, d126352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23057 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108422 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108423 q = 1) (hb : d126353 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108423, d126353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108423, d126353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108424 q = 1) (hb : d126763 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108424, d126763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108424, d126763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108425 q = 1) (hb : d126764 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108425, d126764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108425, d126764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108429 q = 1) (hb : d126766 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108429, d126766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108429, d126766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23058 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108431 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108432 q = 1) (hb : d126767 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108432, d126767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108432, d126767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108433 q = 1) (hb : d126768 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108433, d126768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108433, d126768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d108434 q = 1) (hb : d126769 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108434, d126769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108434, d126769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d108435 q = 1) (hb : d126770 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108435, d126770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108435, d126770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108493 q = 1) (hb : d126777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108493, d126777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108493, d126777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23059 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108500 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108501 q = 1) (hb : d126778 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108501, d126778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108501, d126778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108502 q = 1) (hb : d126779 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108502, d126779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108502, d126779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108503 q = 1) (hb : d126780 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108503, d126780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108503, d126780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108504 q = 1) (hb : d126781 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108504, d126781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108504, d126781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108505 q = 1) (hb : d126782 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108505, d126782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108505, d126782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23061 (p : Pattern) (ha : d108511 p = 1) (hb : d126788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108506 q = 1) (hb : d126783 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108506, d126783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108506, d126783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23060 q ha hb
  have h2 (q : Pattern) (ha : d108507 q = 1) (hb : d126784 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108507, d126784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108507, d126784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108508 q = 1) (hb : d126785 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108508, d126785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108508, d126785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108509 q = 1) (hb : d126786 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108509, d126786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108509, d126786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108510 q = 1) (hb : d126787 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108510, d126787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108510, d126787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108511 q = 1) (hb : d126788 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108511, d126788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108511, d126788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23062 (p : Pattern) (ha : d108607 p = 1) (hb : d126483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d108588 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108540 q = 1) (hb : d126478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d126478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22956 q ha hb
    | true =>
      simp only [d108540, d126478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16095 q hb ha
  have h5 (q : Pattern) (ha : d108589 q = 1) (hb : d126479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108589, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d108603 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108604 q = 1) (hb : d126480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108604, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108605 q = 1) (hb : d126481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108605, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108606 q = 1) (hb : d126482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108606, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108607 q = 1) (hb : d126483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108607, d126483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108607, d126483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro23063 (p : Pattern) (ha : d108628 p = 1) (hb : d126492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108566 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108588 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108540 q = 1) (hb : d126478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d126478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22956 q ha hb
    | true =>
      simp only [d108540, d126478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16095 q hb ha
  have h4 (q : Pattern) (ha : d108589 q = 1) (hb : d126479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108589, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d108603 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108604 q = 1) (hb : d126480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108604, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108605 q = 1) (hb : d126481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108605, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108606 q = 1) (hb : d126482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108606, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108613 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d108618 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d108620 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d108550 q = 1) (hb : d126487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108550, d126487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22958 q ha hb
    | true =>
      simp only [d108550, d126487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16098 q hb ha
  have h13 (q : Pattern) (ha : d108621 q = 1) (hb : d126488 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108621, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108624 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108625 q = 1) (hb : d126489 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108625, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108626 q = 1) (hb : d126490 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108626, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108626, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108627 q = 1) (hb : d126491 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108627, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108627, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108628 q = 1) (hb : d126492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108628, d126492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108628, d126492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro23064 (p : Pattern) (ha : d108648 p = 1) (hb : d126795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108550 q = 1) (hb : d126487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108550, d126487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22958 q ha hb
    | true =>
      simp only [d108550, d126487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16098 q hb ha
  have h3 (q : Pattern) (ha : d108621 q = 1) (hb : d126488 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108621, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108624 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108625 q = 1) (hb : d126489 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108625, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108646 q = 1) (hb : d126490 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108646, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108646, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108647 q = 1) (hb : d126491 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108647, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108647, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108648 q = 1) (hb : d126795 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108648, d126795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108648, d126795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23065 (p : Pattern) (ha : d108712 p = 1) (hb : d126806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108693 q = 1) (hb : d126801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108693, d126801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22980 q ha hb
    | true =>
      simp only [d108693, d126801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16104 q hb ha
  have h3 (q : Pattern) (ha : d108694 q = 1) (hb : d126802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108694, d126802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108694, d126802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108708 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108709 q = 1) (hb : d126803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108709, d126803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108709, d126803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108710 q = 1) (hb : d126804 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108710, d126804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108710, d126804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108711 q = 1) (hb : d126805 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108711, d126805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108711, d126805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108712 q = 1) (hb : d126806 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108712, d126806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108712, d126806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23066 (p : Pattern) (ha : d108725 p = 1) (hb : d126812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108558 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108629 q = 1) (hb : d126493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108629, d126493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23062 q ha hb
    | true =>
      simp only [d108629, d126493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23063 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108642 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108643 q = 1) (hb : d126494 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108643, d126494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108643, d126494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108644 q = 1) (hb : d126793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108644, d126793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108644, d126793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108645 q = 1) (hb : d126794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108645, d126794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108645, d126794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108649 q = 1) (hb : d126796 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108649, d126796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108649, d126796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23064 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108651 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108652 q = 1) (hb : d126797 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108652, d126797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108652, d126797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108653 q = 1) (hb : d126798 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108653, d126798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108653, d126798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d108654 q = 1) (hb : d126799 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108654, d126799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108654, d126799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d108655 q = 1) (hb : d126800 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108655, d126800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108655, d126800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108713 q = 1) (hb : d126807 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108713, d126807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108713, d126807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23065 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108720 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108721 q = 1) (hb : d126808 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108721, d126808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108721, d126808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108722 q = 1) (hb : d126809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108722, d126809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108722, d126809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108723 q = 1) (hb : d126810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108723, d126810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108723, d126810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108724 q = 1) (hb : d126811 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108724, d126811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108724, d126811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108725 q = 1) (hb : d126812 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108725, d126812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108725, d126812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23067 (p : Pattern) (ha : d108731 p = 1) (hb : d126818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108726 q = 1) (hb : d126813 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108726, d126813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108726, d126813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23066 q ha hb
  have h2 (q : Pattern) (ha : d108727 q = 1) (hb : d126814 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108727, d126814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108727, d126814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108728 q = 1) (hb : d126815 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108728, d126815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108728, d126815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108729 q = 1) (hb : d126816 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108729, d126816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108729, d126816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108730 q = 1) (hb : d126817 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108730, d126817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108730, d126817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108731 q = 1) (hb : d126818 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108731, d126818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108731, d126818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23068 (p : Pattern) (ha : d108737 p = 1) (hb : d126824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d107858 q = 1) (hb : d126705 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d107858, d126705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23037 q ha hb
    | true =>
      simp only [d107858, d126705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23043 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108075 q = 1) (hb : d126732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108075, d126732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108075, d126732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23049 q ha hb
  have h3 (q : Pattern) (ha : d108076 q = 1) (hb : d126733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108076, d126733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108076, d126733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108293 q = 1) (hb : d126760 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108293, d126760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108293, d126760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23055 q ha hb
  have h5 (q : Pattern) (ha : d108294 q = 1) (hb : d126761 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108294, d126761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108294, d126761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108295 q = 1) (hb : d126762 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108295, d126762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108295, d126762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108512 q = 1) (hb : d126789 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108512, d126789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108512, d126789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23061 q ha hb
  have h8 (q : Pattern) (ha : d108513 q = 1) (hb : d126790 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108513, d126790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108513, d126790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108514 q = 1) (hb : d126791 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108514, d126791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108514, d126791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108515 q = 1) (hb : d126792 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108515, d126792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108515, d126792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108732 q = 1) (hb : d126819 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108732, d126819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108732, d126819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23067 q ha hb
  have h12 (q : Pattern) (ha : d108733 q = 1) (hb : d126820 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108733, d126820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108733, d126820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108734 q = 1) (hb : d126821 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108734, d126821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108734, d126821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108735 q = 1) (hb : d126822 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108735, d126822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108735, d126822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108736 q = 1) (hb : d126823 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d108736, d126823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108736, d126823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108737 q = 1) (hb : d126824 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d108737, d126824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108737, d126824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro23069 (p : Pattern) (ha : d108743 p = 1) (hb : d126830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108738 q = 1) (hb : d126825 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d108738, d126825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23068 q ha hb
    | true =>
      simp only [d108738, d126825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108739 q = 1) (hb : d126826 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d108739, d126826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108739, d126826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108740 q = 1) (hb : d126827 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d108740, d126827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108740, d126827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108741 q = 1) (hb : d126828 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d108741, d126828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108741, d126828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108742 q = 1) (hb : d126829 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d108742, d126829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108742, d126829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108743 q = 1) (hb : d126830 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d108743, d126830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108743, d126830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23070 (p : Pattern) (ha : d108749 p = 1) (hb : d126836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108744 q = 1) (hb : d126831 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d108744, d126831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23069 q ha hb
    | true =>
      simp only [d108744, d126831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108745 q = 1) (hb : d126832 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d108745, d126832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108745, d126832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108746 q = 1) (hb : d126833 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d108746, d126833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108746, d126833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108747 q = 1) (hb : d126834 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d108747, d126834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108747, d126834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108748 q = 1) (hb : d126835 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d108748, d126835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108748, d126835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108749 q = 1) (hb : d126836 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d108749, d126836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108749, d126836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23071 (p : Pattern) (ha : d108755 p = 1) (hb : d126842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108750 q = 1) (hb : d126837 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d108750, d126837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23070 q ha hb
    | true =>
      simp only [d108750, d126837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108751 q = 1) (hb : d126838 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d108751, d126838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108751, d126838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108752 q = 1) (hb : d126839 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d108752, d126839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108752, d126839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108753 q = 1) (hb : d126840 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d108753, d126840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108753, d126840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108754 q = 1) (hb : d126841 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d108754, d126841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108754, d126841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108755 q = 1) (hb : d126842 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d108755, d126842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108755, d126842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23072 (p : Pattern) (ha : d108761 p = 1) (hb : d126848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108756 q = 1) (hb : d126843 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d108756, d126843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23071 q ha hb
    | true =>
      simp only [d108756, d126843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108757 q = 1) (hb : d126844 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d108757, d126844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108757, d126844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108758 q = 1) (hb : d126845 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d108758, d126845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108758, d126845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108759 q = 1) (hb : d126846 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d108759, d126846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108759, d126846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108760 q = 1) (hb : d126847 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d108760, d126847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108760, d126847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108761 q = 1) (hb : d126848 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d108761, d126848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108761, d126848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23073 (p : Pattern) (ha : d108767 p = 1) (hb : d126854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108762 q = 1) (hb : d126849 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d108762, d126849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23072 q ha hb
    | true =>
      simp only [d108762, d126849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108763 q = 1) (hb : d126850 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d108763, d126850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108763, d126850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108764 q = 1) (hb : d126851 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d108764, d126851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108764, d126851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108765 q = 1) (hb : d126852 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d108765, d126852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108765, d126852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108766 q = 1) (hb : d126853 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d108766, d126853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108766, d126853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108767 q = 1) (hb : d126854 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d108767, d126854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108767, d126854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23074 (p : Pattern) (ha : d108773 p = 1) (hb : d126860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108768 q = 1) (hb : d126855 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d108768, d126855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23073 q ha hb
    | true =>
      simp only [d108768, d126855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108769 q = 1) (hb : d126856 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d108769, d126856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108769, d126856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108770 q = 1) (hb : d126857 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d108770, d126857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108770, d126857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108771 q = 1) (hb : d126858 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d108771, d126858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108771, d126858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108772 q = 1) (hb : d126859 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d108772, d126859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108772, d126859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108773 q = 1) (hb : d126860 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d108773, d126860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108773, d126860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23075 (p : Pattern) (ha : d108779 p = 1) (hb : d126866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108774 q = 1) (hb : d126861 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d108774, d126861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23074 q ha hb
    | true =>
      simp only [d108774, d126861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108775 q = 1) (hb : d126862 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d108775, d126862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108775, d126862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108776 q = 1) (hb : d126863 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d108776, d126863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108776, d126863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108777 q = 1) (hb : d126864 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d108777, d126864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108777, d126864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108778 q = 1) (hb : d126865 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d108778, d126865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108778, d126865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108779 q = 1) (hb : d126866 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d108779, d126866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108779, d126866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23076 (p : Pattern) (ha : d108822 p = 1) (hb : d125811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d125757 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108818 q = 1) (hb : d125807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108818, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10774 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108819 q = 1) (hb : d125808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108819, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108820 q = 1) (hb : d125809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108820, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108821 q = 1) (hb : d125810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108821, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108822 q = 1) (hb : d125811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108822, d125811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108822, d125811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro23077 (p : Pattern) (ha : d108827 p = 1) (hb : d125818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d125757 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108818 q = 1) (hb : d125807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108818, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10774 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108819 q = 1) (hb : d125808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108819, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108820 q = 1) (hb : d125809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108820, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108821 q = 1) (hb : d125810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108821, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10783 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10787 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10789 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d125764 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108823 q = 1) (hb : d125814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108823, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10795 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108824 q = 1) (hb : d125815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108824, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108825 q = 1) (hb : d125816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108825, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108825, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108826 q = 1) (hb : d125817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108826, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108826, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108827 q = 1) (hb : d125818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108827, d125818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108827, d125818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro23078 (p : Pattern) (ha : d108834 p = 1) (hb : d126656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10789 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d125764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108823 q = 1) (hb : d125814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108823, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10795 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108824 q = 1) (hb : d125815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108824, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108832 q = 1) (hb : d125816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108832, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108832, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108833 q = 1) (hb : d125817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108833, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108833, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108834 q = 1) (hb : d126656 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108834, d126656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108834, d126656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23079 (p : Pattern) (ha : d108844 p = 1) (hb : d126666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d125790 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108840 q = 1) (hb : d126662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108840, d126662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108840, d126662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10846 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108841 q = 1) (hb : d126663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108841, d126663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108841, d126663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108842 q = 1) (hb : d126664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108842, d126664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108842, d126664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108843 q = 1) (hb : d126665 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108843, d126665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108843, d126665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108844 q = 1) (hb : d126666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108844, d126666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108844, d126666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23080 (p : Pattern) (ha : d108850 p = 1) (hb : d126672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10729 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108828 q = 1) (hb : d125819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108828, d125819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23076 q ha hb
    | true =>
      simp only [d108828, d125819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23077 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10802 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108829 q = 1) (hb : d125820 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108829, d125820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108829, d125820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108830 q = 1) (hb : d126654 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108830, d126654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108830, d126654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108831 q = 1) (hb : d126655 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108831, d126655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108831, d126655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108835 q = 1) (hb : d126657 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108835, d126657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108835, d126657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23078 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108836 q = 1) (hb : d126658 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108836, d126658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108836, d126658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108837 q = 1) (hb : d126659 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108837, d126659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108837, d126659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108838 q = 1) (hb : d126660 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108838, d126660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108838, d126660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108839 q = 1) (hb : d126661 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108839, d126661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108839, d126661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108845 q = 1) (hb : d126667 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108845, d126667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108845, d126667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23079 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108846 q = 1) (hb : d126668 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108846, d126668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108846, d126668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108847 q = 1) (hb : d126669 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108847, d126669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108847, d126669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108848 q = 1) (hb : d126670 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108848, d126670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108848, d126670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108849 q = 1) (hb : d126671 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108849, d126671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108849, d126671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108850 q = 1) (hb : d126672 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108850, d126672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108850, d126672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23081 (p : Pattern) (ha : d108856 p = 1) (hb : d126678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d108813 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d108813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d108813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16225 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d108814 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d108814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d108814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d108815 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d108815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d108815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d108816 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d108816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d108816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d108817 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d108817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d108817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108851 q = 1) (hb : d126673 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108851, d126673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108851, d126673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23080 q ha hb
  have h8 (q : Pattern) (ha : d108852 q = 1) (hb : d126674 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108852, d126674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108852, d126674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108853 q = 1) (hb : d126675 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108853, d126675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108853, d126675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108854 q = 1) (hb : d126676 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108854, d126676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108854, d126676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108855 q = 1) (hb : d126677 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108855, d126677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108855, d126677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108856 q = 1) (hb : d126678 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108856, d126678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d108856, d126678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro23082 (p : Pattern) (ha : d108861 p = 1) (hb : d125930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10906 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10915 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10928 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d125925 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108857 q = 1) (hb : d125926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108857, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10957 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108858 q = 1) (hb : d125927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108858, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108859 q = 1) (hb : d125928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108859, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108860 q = 1) (hb : d125929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108860, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108861 q = 1) (hb : d125930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108861, d125930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108861, d125930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro23083 (p : Pattern) (ha : d108866 p = 1) (hb : d125939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10906 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10915 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10928 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d125925 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108857 q = 1) (hb : d125926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108857, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10957 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108858 q = 1) (hb : d125927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108858, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108859 q = 1) (hb : d125928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108859, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108860 q = 1) (hb : d125929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108860, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10967 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10972 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10974 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d125934 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108862 q = 1) (hb : d125935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108862, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108863 q = 1) (hb : d125936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108863, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108864 q = 1) (hb : d125937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108864, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108864, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108865 q = 1) (hb : d125938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108865, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108865, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108866 q = 1) (hb : d125939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108866, d125939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108866, d125939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro23084 (p : Pattern) (ha : d108873 p = 1) (hb : d126681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d125934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108862 q = 1) (hb : d125935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108862, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10981 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108863 q = 1) (hb : d125936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108863, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108871 q = 1) (hb : d125937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108871, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108871, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108872 q = 1) (hb : d125938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108872, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108872, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108873 q = 1) (hb : d126681 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108873, d126681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108873, d126681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23085 (p : Pattern) (ha : d108883 p = 1) (hb : d126692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126687 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108879 q = 1) (hb : d126688 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108879, d126688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108879, d126688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11067 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108880 q = 1) (hb : d126689 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108880, d126689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108880, d126689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108881 q = 1) (hb : d126690 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108881, d126690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108881, d126690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108882 q = 1) (hb : d126691 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108882, d126691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108882, d126691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108883 q = 1) (hb : d126692 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108883, d126692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108883, d126692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23086 (p : Pattern) (ha : d108889 p = 1) (hb : d126698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10898 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108867 q = 1) (hb : d125940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108867, d125940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23082 q ha hb
    | true =>
      simp only [d108867, d125940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23083 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10999 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108868 q = 1) (hb : d125941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108868, d125941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108868, d125941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108869 q = 1) (hb : d126679 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108869, d126679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108869, d126679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108870 q = 1) (hb : d126680 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108870, d126680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108870, d126680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108874 q = 1) (hb : d126682 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108874, d126682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108874, d126682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23084 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11008 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108875 q = 1) (hb : d126683 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108875, d126683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108875, d126683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108876 q = 1) (hb : d126684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108876, d126684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108876, d126684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108877 q = 1) (hb : d126685 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108877, d126685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108877, d126685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108878 q = 1) (hb : d126686 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108878, d126686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108878, d126686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108884 q = 1) (hb : d126693 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108884, d126693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108884, d126693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23085 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108885 q = 1) (hb : d126694 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108885, d126694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108885, d126694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108886 q = 1) (hb : d126695 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108886, d126695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108886, d126695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108887 q = 1) (hb : d126696 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108887, d126696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108887, d126696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108888 q = 1) (hb : d126697 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108888, d126697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108888, d126697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108889 q = 1) (hb : d126698 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108889, d126698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108889, d126698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23087 (p : Pattern) (ha : d108895 p = 1) (hb : d126704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108890 q = 1) (hb : d126699 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108890, d126699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108890, d126699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23086 q ha hb
  have h2 (q : Pattern) (ha : d108891 q = 1) (hb : d126700 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108891, d126700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108891, d126700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108892 q = 1) (hb : d126701 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108892, d126701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108892, d126701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108893 q = 1) (hb : d126702 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108893, d126702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108893, d126702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108894 q = 1) (hb : d126703 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108894, d126703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108894, d126703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108895 q = 1) (hb : d126704 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108895, d126704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108895, d126704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23088 (p : Pattern) (ha : d108901 p = 1) (hb : d126063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11155 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d126058 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108897 q = 1) (hb : d126059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108897, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d11208 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108898 q = 1) (hb : d126060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108898, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108899 q = 1) (hb : d126061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108899, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108900 q = 1) (hb : d126062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108900, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108901 q = 1) (hb : d126063 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108901, d126063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108901, d126063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro23089 (p : Pattern) (ha : d108906 p = 1) (hb : d126072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11146 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11155 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11168 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126058 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108897 q = 1) (hb : d126059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108897, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d11208 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108898 q = 1) (hb : d126060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108898, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108899 q = 1) (hb : d126061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108899, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108900 q = 1) (hb : d126062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108900, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d11218 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d11223 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d11225 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d126067 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108902 q = 1) (hb : d126068 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108902, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11232 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108903 q = 1) (hb : d126069 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108903, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108904 q = 1) (hb : d126070 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108904, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108904, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108905 q = 1) (hb : d126071 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108905, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108905, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108906 q = 1) (hb : d126072 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108906, d126072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108906, d126072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro23090 (p : Pattern) (ha : d108913 p = 1) (hb : d126708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11225 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126067 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108902 q = 1) (hb : d126068 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108902, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11232 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108903 q = 1) (hb : d126069 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108903, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108911 q = 1) (hb : d126070 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108911, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108911, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108912 q = 1) (hb : d126071 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108912, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108912, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108913 q = 1) (hb : d126708 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108913, d126708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108913, d126708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23091 (p : Pattern) (ha : d108923 p = 1) (hb : d126719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11296 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126714 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108919 q = 1) (hb : d126715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108919, d126715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108919, d126715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11336 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108920 q = 1) (hb : d126716 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108920, d126716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108920, d126716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108921 q = 1) (hb : d126717 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108921, d126717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108921, d126717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108922 q = 1) (hb : d126718 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108922, d126718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108922, d126718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108923 q = 1) (hb : d126719 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108923, d126719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108923, d126719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23092 (p : Pattern) (ha : d108929 p = 1) (hb : d126725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11138 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108907 q = 1) (hb : d126073 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108907, d126073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23088 q ha hb
    | true =>
      simp only [d108907, d126073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23089 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11250 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108908 q = 1) (hb : d126074 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108908, d126074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108908, d126074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108909 q = 1) (hb : d126706 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108909, d126706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108909, d126706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108910 q = 1) (hb : d126707 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108910, d126707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108910, d126707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108914 q = 1) (hb : d126709 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108914, d126709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108914, d126709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23090 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11259 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108915 q = 1) (hb : d126710 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108915, d126710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108915, d126710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108916 q = 1) (hb : d126711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108916, d126711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108916, d126711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108917 q = 1) (hb : d126712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108917, d126712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108917, d126712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108918 q = 1) (hb : d126713 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108918, d126713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108918, d126713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108924 q = 1) (hb : d126720 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108924, d126720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108924, d126720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23091 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11352 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108925 q = 1) (hb : d126721 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108925, d126721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108925, d126721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108926 q = 1) (hb : d126722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108926, d126722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108926, d126722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108927 q = 1) (hb : d126723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108927, d126723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108927, d126723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108928 q = 1) (hb : d126724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108928, d126724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108928, d126724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108929 q = 1) (hb : d126725 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108929, d126725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108929, d126725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23093 (p : Pattern) (ha : d108935 p = 1) (hb : d126731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108930 q = 1) (hb : d126726 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108930, d126726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108930, d126726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23092 q ha hb
  have h2 (q : Pattern) (ha : d108931 q = 1) (hb : d126727 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108931, d126727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108931, d126727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108932 q = 1) (hb : d126728 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108932, d126728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108932, d126728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108933 q = 1) (hb : d126729 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108933, d126729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108933, d126729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108934 q = 1) (hb : d126730 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108934, d126730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108934, d126730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108935 q = 1) (hb : d126731 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108935, d126731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108935, d126731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23094 (p : Pattern) (ha : d108942 p = 1) (hb : d126202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11425 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11438 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d126197 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108938 q = 1) (hb : d126198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108938, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d11478 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108939 q = 1) (hb : d126199 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108939, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108940 q = 1) (hb : d126200 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108940, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108941 q = 1) (hb : d126201 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108941, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108942 q = 1) (hb : d126202 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108942, d126202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108942, d126202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro23095 (p : Pattern) (ha : d108947 p = 1) (hb : d126211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11425 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11438 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126197 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108938 q = 1) (hb : d126198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108938, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d11478 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108939 q = 1) (hb : d126199 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108939, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108940 q = 1) (hb : d126200 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108940, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108941 q = 1) (hb : d126201 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108941, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d11488 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d11493 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d11495 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d126206 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108943 q = 1) (hb : d126207 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108943, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11502 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108944 q = 1) (hb : d126208 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108944, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108945 q = 1) (hb : d126209 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108945, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108945, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108946 q = 1) (hb : d126210 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108946, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108946, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108947 q = 1) (hb : d126211 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108947, d126211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108947, d126211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro23096 (p : Pattern) (ha : d108954 p = 1) (hb : d126736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126206 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108943 q = 1) (hb : d126207 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108943, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11502 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108944 q = 1) (hb : d126208 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108944, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108952 q = 1) (hb : d126209 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108952, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108952, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108953 q = 1) (hb : d126210 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108953, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108953, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108954 q = 1) (hb : d126736 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108954, d126736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108954, d126736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23097 (p : Pattern) (ha : d108964 p = 1) (hb : d126747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126742 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108960 q = 1) (hb : d126743 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108960, d126743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108960, d126743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11606 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108961 q = 1) (hb : d126744 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108961, d126744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108961, d126744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108962 q = 1) (hb : d126745 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108962, d126745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108962, d126745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108963 q = 1) (hb : d126746 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108963, d126746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108963, d126746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108964 q = 1) (hb : d126747 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108964, d126747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108964, d126747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23098 (p : Pattern) (ha : d108970 p = 1) (hb : d126753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11408 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108948 q = 1) (hb : d126212 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108948, d126212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23094 q ha hb
    | true =>
      simp only [d108948, d126212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23095 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11520 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108949 q = 1) (hb : d126213 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108949, d126213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108949, d126213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108950 q = 1) (hb : d126734 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108950, d126734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108950, d126734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108951 q = 1) (hb : d126735 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108951, d126735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108951, d126735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108955 q = 1) (hb : d126737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108955, d126737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108955, d126737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23096 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11529 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108956 q = 1) (hb : d126738 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108956, d126738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108956, d126738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108957 q = 1) (hb : d126739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108957, d126739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108957, d126739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108958 q = 1) (hb : d126740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108958, d126740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108958, d126740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108959 q = 1) (hb : d126741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108959, d126741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108959, d126741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108965 q = 1) (hb : d126748 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108965, d126748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108965, d126748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23097 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11622 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108966 q = 1) (hb : d126749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108966, d126749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108966, d126749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108967 q = 1) (hb : d126750 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108967, d126750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108967, d126750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108968 q = 1) (hb : d126751 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108968, d126751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108968, d126751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108969 q = 1) (hb : d126752 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108969, d126752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108969, d126752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108970 q = 1) (hb : d126753 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108970, d126753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108970, d126753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23099 (p : Pattern) (ha : d108976 p = 1) (hb : d126759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108971 q = 1) (hb : d126754 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108971, d126754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108971, d126754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23098 q ha hb
  have h2 (q : Pattern) (ha : d108972 q = 1) (hb : d126755 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108972, d126755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108972, d126755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108973 q = 1) (hb : d126756 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108973, d126756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108973, d126756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108974 q = 1) (hb : d126757 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108974, d126757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108974, d126757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108975 q = 1) (hb : d126758 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108975, d126758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108975, d126758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108976 q = 1) (hb : d126759 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108976, d126759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108976, d126759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23100 (p : Pattern) (ha : d108984 p = 1) (hb : d126342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11696 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11709 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d126337 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108980 q = 1) (hb : d126338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108980, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d11749 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108981 q = 1) (hb : d126339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108981, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108982 q = 1) (hb : d126340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108982, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108983 q = 1) (hb : d126341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108983, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108984 q = 1) (hb : d126342 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108984, d126342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108984, d126342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro23101 (p : Pattern) (ha : d108989 p = 1) (hb : d126351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11696 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11709 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126337 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108980 q = 1) (hb : d126338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108980, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d11749 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108981 q = 1) (hb : d126339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108981, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108982 q = 1) (hb : d126340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108982, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108983 q = 1) (hb : d126341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108983, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d11759 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d11764 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d11766 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d126346 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108985 q = 1) (hb : d126347 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108985, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11773 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108986 q = 1) (hb : d126348 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108986, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108987 q = 1) (hb : d126349 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108987, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108987, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108988 q = 1) (hb : d126350 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108988, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108988, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108989 q = 1) (hb : d126351 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108989, d126351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108989, d126351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro23102 (p : Pattern) (ha : d108996 p = 1) (hb : d126765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126346 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108985 q = 1) (hb : d126347 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108985, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11773 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108986 q = 1) (hb : d126348 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108986, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108994 q = 1) (hb : d126349 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108994, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108994, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108995 q = 1) (hb : d126350 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108995, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108995, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108996 q = 1) (hb : d126765 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108996, d126765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108996, d126765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23103 (p : Pattern) (ha : d109006 p = 1) (hb : d126776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11837 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109002 q = 1) (hb : d126772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109002, d126772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109002, d126772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11877 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109003 q = 1) (hb : d126773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109003, d126773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109003, d126773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109004 q = 1) (hb : d126774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109004, d126774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109004, d126774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109005 q = 1) (hb : d126775 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109005, d126775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109005, d126775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109006 q = 1) (hb : d126776 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109006, d126776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109006, d126776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23104 (p : Pattern) (ha : d109012 p = 1) (hb : d126782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11679 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108990 q = 1) (hb : d126352 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108990, d126352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23100 q ha hb
    | true =>
      simp only [d108990, d126352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23101 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108991 q = 1) (hb : d126353 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108991, d126353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108991, d126353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108992 q = 1) (hb : d126763 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108992, d126763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108992, d126763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108993 q = 1) (hb : d126764 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108993, d126764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108993, d126764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108997 q = 1) (hb : d126766 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108997, d126766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108997, d126766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23102 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11800 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108998 q = 1) (hb : d126767 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108998, d126767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108998, d126767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108999 q = 1) (hb : d126768 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108999, d126768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108999, d126768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d109000 q = 1) (hb : d126769 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109000, d126769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109000, d126769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d109001 q = 1) (hb : d126770 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109001, d126770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109001, d126770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109007 q = 1) (hb : d126777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109007, d126777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109007, d126777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23103 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11893 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109008 q = 1) (hb : d126778 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109008, d126778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109008, d126778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109009 q = 1) (hb : d126779 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109009, d126779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109009, d126779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d109010 q = 1) (hb : d126780 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109010, d126780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109010, d126780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d109011 q = 1) (hb : d126781 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109011, d126781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109011, d126781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d109012 q = 1) (hb : d126782 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109012, d126782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109012, d126782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23105 (p : Pattern) (ha : d109018 p = 1) (hb : d126788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109013 q = 1) (hb : d126783 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109013, d126783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109013, d126783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23104 q ha hb
  have h2 (q : Pattern) (ha : d109014 q = 1) (hb : d126784 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109014, d126784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109014, d126784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109015 q = 1) (hb : d126785 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109015, d126785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109015, d126785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109016 q = 1) (hb : d126786 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109016, d126786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109016, d126786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109017 q = 1) (hb : d126787 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109017, d126787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109017, d126787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109018 q = 1) (hb : d126788 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109018, d126788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109018, d126788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23106 (p : Pattern) (ha : d109027 p = 1) (hb : d126483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11959 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11968 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11981 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d126478 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109023 q = 1) (hb : d126479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d109023, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12021 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d109024 q = 1) (hb : d126480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109024, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d109025 q = 1) (hb : d126481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109025, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109026 q = 1) (hb : d126482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109026, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109027 q = 1) (hb : d126483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109027, d126483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109027, d126483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro23107 (p : Pattern) (ha : d109032 p = 1) (hb : d126492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11959 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11968 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126478 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d109023 q = 1) (hb : d126479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109023, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12021 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d109024 q = 1) (hb : d126480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109024, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d109025 q = 1) (hb : d126481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109025, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109026 q = 1) (hb : d126482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109026, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12031 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12036 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12038 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d126487 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d109028 q = 1) (hb : d126488 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d109028, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12045 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109029 q = 1) (hb : d126489 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109029, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109030 q = 1) (hb : d126490 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109030, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d109030, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109031 q = 1) (hb : d126491 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109031, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d109031, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d109032 q = 1) (hb : d126492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109032, d126492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109032, d126492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro23108 (p : Pattern) (ha : d109039 p = 1) (hb : d126795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126487 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109028 q = 1) (hb : d126488 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109028, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109029 q = 1) (hb : d126489 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109029, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109037 q = 1) (hb : d126490 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109037, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109037, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109038 q = 1) (hb : d126491 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109038, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109038, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109039 q = 1) (hb : d126795 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109039, d126795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109039, d126795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23109 (p : Pattern) (ha : d109049 p = 1) (hb : d126806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12109 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126801 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109045 q = 1) (hb : d126802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109045, d126802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109045, d126802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12149 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109046 q = 1) (hb : d126803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109046, d126803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109046, d126803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109047 q = 1) (hb : d126804 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109047, d126804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109047, d126804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109048 q = 1) (hb : d126805 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109048, d126805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109048, d126805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109049 q = 1) (hb : d126806 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109049, d126806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109049, d126806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23110 (p : Pattern) (ha : d109055 p = 1) (hb : d126812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109033 q = 1) (hb : d126493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109033, d126493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23106 q ha hb
    | true =>
      simp only [d109033, d126493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23107 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12063 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109034 q = 1) (hb : d126494 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109034, d126494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109034, d126494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109035 q = 1) (hb : d126793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109035, d126793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109035, d126793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109036 q = 1) (hb : d126794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109036, d126794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109036, d126794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109040 q = 1) (hb : d126796 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109040, d126796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109040, d126796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23108 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12072 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d109041 q = 1) (hb : d126797 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109041, d126797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109041, d126797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d109042 q = 1) (hb : d126798 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109042, d126798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109042, d126798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d109043 q = 1) (hb : d126799 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109043, d126799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109043, d126799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d109044 q = 1) (hb : d126800 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109044, d126800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109044, d126800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109050 q = 1) (hb : d126807 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109050, d126807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109050, d126807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23109 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12165 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109051 q = 1) (hb : d126808 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109051, d126808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109051, d126808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109052 q = 1) (hb : d126809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109052, d126809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109052, d126809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d109053 q = 1) (hb : d126810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109053, d126810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109053, d126810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d109054 q = 1) (hb : d126811 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109054, d126811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109054, d126811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d109055 q = 1) (hb : d126812 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109055, d126812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109055, d126812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro23111 (p : Pattern) (ha : d109061 p = 1) (hb : d126818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109056 q = 1) (hb : d126813 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109056, d126813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109056, d126813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23110 q ha hb
  have h2 (q : Pattern) (ha : d109057 q = 1) (hb : d126814 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109057, d126814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109057, d126814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109058 q = 1) (hb : d126815 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109058, d126815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109058, d126815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109059 q = 1) (hb : d126816 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109059, d126816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109059, d126816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109060 q = 1) (hb : d126817 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109060, d126817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109060, d126817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109061 q = 1) (hb : d126818 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109061, d126818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109061, d126818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23112 (p : Pattern) (ha : d109067 p = 1) (hb : d126824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d108896 q = 1) (hb : d126705 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108896, d126705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23081 q ha hb
    | true =>
      simp only [d108896, d126705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23087 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108936 q = 1) (hb : d126732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108936, d126732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108936, d126732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23093 q ha hb
  have h3 (q : Pattern) (ha : d108937 q = 1) (hb : d126733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108937, d126733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108937, d126733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108977 q = 1) (hb : d126760 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108977, d126760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108977, d126760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23099 q ha hb
  have h5 (q : Pattern) (ha : d108978 q = 1) (hb : d126761 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108978, d126761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108978, d126761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108979 q = 1) (hb : d126762 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108979, d126762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108979, d126762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109019 q = 1) (hb : d126789 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109019, d126789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109019, d126789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23105 q ha hb
  have h8 (q : Pattern) (ha : d109020 q = 1) (hb : d126790 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109020, d126790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109020, d126790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109021 q = 1) (hb : d126791 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109021, d126791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109021, d126791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109022 q = 1) (hb : d126792 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109022, d126792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109022, d126792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109062 q = 1) (hb : d126819 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109062, d126819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109062, d126819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23111 q ha hb
  have h12 (q : Pattern) (ha : d109063 q = 1) (hb : d126820 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109063, d126820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109063, d126820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109064 q = 1) (hb : d126821 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109064, d126821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109064, d126821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109065 q = 1) (hb : d126822 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109065, d126822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109065, d126822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109066 q = 1) (hb : d126823 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109066, d126823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109066, d126823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109067 q = 1) (hb : d126824 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109067, d126824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109067, d126824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro23113 (p : Pattern) (ha : d109073 p = 1) (hb : d126830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109068 q = 1) (hb : d126825 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109068, d126825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23112 q ha hb
    | true =>
      simp only [d109068, d126825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109069 q = 1) (hb : d126826 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109069, d126826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109069, d126826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109070 q = 1) (hb : d126827 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109070, d126827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109070, d126827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109071 q = 1) (hb : d126828 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109071, d126828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109071, d126828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109072 q = 1) (hb : d126829 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109072, d126829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109072, d126829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109073 q = 1) (hb : d126830 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109073, d126830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109073, d126830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23114 (p : Pattern) (ha : d109079 p = 1) (hb : d126836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109074 q = 1) (hb : d126831 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109074, d126831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23113 q ha hb
    | true =>
      simp only [d109074, d126831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109075 q = 1) (hb : d126832 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109075, d126832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109075, d126832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109076 q = 1) (hb : d126833 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109076, d126833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109076, d126833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109077 q = 1) (hb : d126834 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109077, d126834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109077, d126834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109078 q = 1) (hb : d126835 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109078, d126835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109078, d126835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109079 q = 1) (hb : d126836 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109079, d126836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109079, d126836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23115 (p : Pattern) (ha : d109085 p = 1) (hb : d126842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109080 q = 1) (hb : d126837 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109080, d126837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23114 q ha hb
    | true =>
      simp only [d109080, d126837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109081 q = 1) (hb : d126838 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109081, d126838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109081, d126838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109082 q = 1) (hb : d126839 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109082, d126839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109082, d126839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109083 q = 1) (hb : d126840 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109083, d126840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109083, d126840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109084 q = 1) (hb : d126841 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109084, d126841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109084, d126841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109085 q = 1) (hb : d126842 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109085, d126842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109085, d126842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23116 (p : Pattern) (ha : d109091 p = 1) (hb : d126848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109086 q = 1) (hb : d126843 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109086, d126843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23115 q ha hb
    | true =>
      simp only [d109086, d126843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109087 q = 1) (hb : d126844 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109087, d126844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109087, d126844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109088 q = 1) (hb : d126845 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109088, d126845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109088, d126845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109089 q = 1) (hb : d126846 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109089, d126846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109089, d126846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109090 q = 1) (hb : d126847 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109090, d126847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109090, d126847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109091 q = 1) (hb : d126848 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109091, d126848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109091, d126848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23117 (p : Pattern) (ha : d109097 p = 1) (hb : d126854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109092 q = 1) (hb : d126849 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109092, d126849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23116 q ha hb
    | true =>
      simp only [d109092, d126849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109093 q = 1) (hb : d126850 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109093, d126850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109093, d126850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109094 q = 1) (hb : d126851 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109094, d126851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109094, d126851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109095 q = 1) (hb : d126852 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109095, d126852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109095, d126852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109096 q = 1) (hb : d126853 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109096, d126853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109096, d126853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109097 q = 1) (hb : d126854 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109097, d126854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109097, d126854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23118 (p : Pattern) (ha : d109103 p = 1) (hb : d126860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109098 q = 1) (hb : d126855 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109098, d126855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23117 q ha hb
    | true =>
      simp only [d109098, d126855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109099 q = 1) (hb : d126856 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109099, d126856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109099, d126856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109100 q = 1) (hb : d126857 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109100, d126857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109100, d126857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109101 q = 1) (hb : d126858 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109101, d126858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109101, d126858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109102 q = 1) (hb : d126859 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109102, d126859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109102, d126859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109103 q = 1) (hb : d126860 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109103, d126860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109103, d126860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23119 (p : Pattern) (ha : d109109 p = 1) (hb : d126866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109104 q = 1) (hb : d126861 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109104, d126861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23118 q ha hb
    | true =>
      simp only [d109104, d126861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109105 q = 1) (hb : d126862 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109105, d126862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109105, d126862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109106 q = 1) (hb : d126863 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109106, d126863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109106, d126863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109107 q = 1) (hb : d126864 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109107, d126864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109107, d126864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109108 q = 1) (hb : d126865 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109108, d126865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109108, d126865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109109 q = 1) (hb : d126866 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109109, d126866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109109, d126866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23120 (p : Pattern) (ha : d0 p = 1) (hb : d126873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126873 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro23121 (p : Pattern) (ha : d0 p = 1) (hb : d128190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128190 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro23122 (p : Pattern) (ha : d0 p = 1) (hb : d128482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128482 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro23123 (p : Pattern) (ha : d0 p = 1) (hb : d128487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128487 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro23124 (p : Pattern) (ha : d0 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro23125 (p : Pattern) (ha : d0 p = 1) (hb : d129310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129310 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro23126 (p : Pattern) (ha : d0 p = 1) (hb : d129470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129470 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro23127 (p : Pattern) (ha : d0 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro23128 (p : Pattern) (ha : d0 p = 1) (hb : d123878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123878 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro23129 (p : Pattern) (ha : d0 p = 1) (hb : d125742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125742 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro23130 (p : Pattern) (ha : d9302 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9301 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9302 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9302, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9302, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23131 (p : Pattern) (ha : d9308 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9303 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23130 q ha hb
    | true =>
      simp only [d9303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9304 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9305 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9306 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9307 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9308 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23132 (p : Pattern) (ha : d9314 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9309 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23131 q ha hb
    | true =>
      simp only [d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9310 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9311 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9312 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9313 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9314 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23133 (p : Pattern) (ha : d9320 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9315 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23132 q ha hb
  have h2 (q : Pattern) (ha : d9316 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9317 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9318 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d9318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9319 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d9319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9320 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d9320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23134 (p : Pattern) (ha : d9335 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9335 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9335, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9335, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23135 (p : Pattern) (ha : d9341 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9336 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23134 q ha hb
    | true =>
      simp only [d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9337 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9303 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23130 q ha hb
    | true =>
      simp only [d9303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9304 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9338 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9339 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9340 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9341 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23136 (p : Pattern) (ha : d100941 p = 1) (hb : d101879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9342 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23135 q ha hb
    | true =>
      simp only [d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23131 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101875 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d9309 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23131 q ha hb
    | true =>
      simp only [d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9310 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101876 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101877 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101878 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d101879 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23137 (p : Pattern) (ha : d100941 p = 1) (hb : d101885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d101880 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23136 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101881 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d101882 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d101883 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101884 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101885 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23138 (p : Pattern) (ha : d9436 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9309 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23131 q ha hb
    | true =>
      simp only [d9309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9432 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9433 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9434 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9435 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9436 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23139 (p : Pattern) (ha : d9394 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9393 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9394 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9394, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9394, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23140 (p : Pattern) (ha : d9400 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9395 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23139 q ha hb
    | true =>
      simp only [d9395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9396 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9336 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23134 q ha hb
    | true =>
      simp only [d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9337 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9397 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9398 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9399 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9400 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23141 (p : Pattern) (ha : d9424 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9336 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23134 q ha hb
    | true =>
      simp only [d9336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9337 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9421 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9422 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9423 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9424 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23142 (p : Pattern) (ha : d100941 p = 1) (hb : d101895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9401 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23140 q ha hb
    | true =>
      simp only [d9401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23135 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d9425 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23141 q ha hb
    | true =>
      simp only [d9425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9426 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101893 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101894 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d101895 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23143 (p : Pattern) (ha : d100941 p = 1) (hb : d101901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d101896 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23142 q ha hb
  have h2 (q : Pattern) (ha : d9437 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23138 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d101897 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d101898 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101899 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101900 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101901 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23144 (p : Pattern) (ha : d100941 p = 1) (hb : d101907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9321 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d9321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23133 q ha hb
  have h2 (q : Pattern) (ha : d9322 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d9322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9323 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d9323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9324 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d9324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101886 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23137 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101887 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101888 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d101889 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d100941 q = 1) (hb : d101890 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d101890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d100941 q = 1) (hb : d101902 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23143 q ha hb
  have h11 (q : Pattern) (ha : d100941 q = 1) (hb : d101903 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d100941 q = 1) (hb : d101904 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d100941 q = 1) (hb : d101905 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d100941 q = 1) (hb : d101906 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d100941 q = 1) (hb : d101907 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d101907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23145 (p : Pattern) (ha : d9497 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9497 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9497, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9497, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23146 (p : Pattern) (ha : d9556 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9498 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23145 q ha hb
    | true =>
      simp only [d9498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9499 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9553 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9554 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9555 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9556 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23147 (p : Pattern) (ha : d9562 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9557 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23146 q ha hb
    | true =>
      simp only [d9557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9558 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9559 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9560 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9561 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9562 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23148 (p : Pattern) (ha : d9484 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9484 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9484, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9484, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23149 (p : Pattern) (ha : d9489 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9488 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9489 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9489, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9489, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23150 (p : Pattern) (ha : d9495 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9485 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23148 q ha hb
    | true =>
      simp only [d9485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9486 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9490 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23149 q ha hb
    | true =>
      simp only [d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9491 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9492 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9493 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9494 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9495 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23151 (p : Pattern) (ha : d9503 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9490 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23149 q ha hb
    | true =>
      simp only [d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9491 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9498 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23145 q ha hb
    | true =>
      simp only [d9498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9499 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9500 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9501 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9502 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9503 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23152 (p : Pattern) (ha : d9545 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9490 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23149 q ha hb
    | true =>
      simp only [d9490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9491 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9542 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9543 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9544 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9545 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23153 (p : Pattern) (ha : d100941 p = 1) (hb : d101912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9504 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23150 q ha hb
    | true =>
      simp only [d9504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23151 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101908 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d9546 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23152 q ha hb
    | true =>
      simp only [d9546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9547 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101909 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101910 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101911 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d101912 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23154 (p : Pattern) (ha : d100941 p = 1) (hb : d101918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d101913 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23153 q ha hb
  have h2 (q : Pattern) (ha : d9563 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23147 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d101914 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d101915 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101916 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101917 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101918 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23155 (p : Pattern) (ha : d100941 p = 1) (hb : d101924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d101919 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23154 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101920 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d101921 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d101922 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101923 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101924 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23156 (p : Pattern) (ha : d9642 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9641 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9642 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9642, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9642, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23157 (p : Pattern) (ha : d9725 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9643 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23156 q ha hb
    | true =>
      simp only [d9643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9644 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9722 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9723 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9724 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9725 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23158 (p : Pattern) (ha : d9731 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9726 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23157 q ha hb
    | true =>
      simp only [d9726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9727 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9728 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9729 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9730 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9731 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23159 (p : Pattern) (ha : d9629 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9628 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9629 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9629, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9629, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23160 (p : Pattern) (ha : d9634 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9633 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9634 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9634, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9634, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23161 (p : Pattern) (ha : d9640 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9630 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23159 q ha hb
    | true =>
      simp only [d9630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9631 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9635 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23160 q ha hb
    | true =>
      simp only [d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9636 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9637 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9638 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9639 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9640 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23162 (p : Pattern) (ha : d9648 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9635 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23160 q ha hb
    | true =>
      simp only [d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9636 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9643 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23156 q ha hb
    | true =>
      simp only [d9643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9644 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9645 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9646 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9647 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9648 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23163 (p : Pattern) (ha : d9714 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9635 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23160 q ha hb
    | true =>
      simp only [d9635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9636 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9711 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9712 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9713 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9714 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23164 (p : Pattern) (ha : d100941 p = 1) (hb : d101930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9649 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23161 q ha hb
    | true =>
      simp only [d9649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23162 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d9715 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23163 q ha hb
    | true =>
      simp only [d9715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9716 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d101930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23165 (p : Pattern) (ha : d100941 p = 1) (hb : d101936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d101931 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23164 q ha hb
  have h2 (q : Pattern) (ha : d9732 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23158 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d101932 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d101933 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101934 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101935 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101936 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23166 (p : Pattern) (ha : d100941 p = 1) (hb : d101942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d101937 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23165 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101938 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d101939 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d101940 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101941 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101942 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23167 (p : Pattern) (ha : d9875 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9874 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9875 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9875, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9875, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23168 (p : Pattern) (ha : d10010 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9876 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23167 q ha hb
    | true =>
      simp only [d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9877 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10007 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10008 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10009 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10010 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23169 (p : Pattern) (ha : d10016 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10011 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23168 q ha hb
    | true =>
      simp only [d10011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10012 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10013 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10014 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10015 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10016 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23170 (p : Pattern) (ha : d9856 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9855 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9856 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9856, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9856, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23171 (p : Pattern) (ha : d9861 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9861 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9861, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9861, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23172 (p : Pattern) (ha : d9867 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9857 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23170 q ha hb
    | true =>
      simp only [d9857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9858 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9862 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23171 q ha hb
    | true =>
      simp only [d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9863 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9864 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9865 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9866 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9867 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23173 (p : Pattern) (ha : d9881 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9862 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23171 q ha hb
    | true =>
      simp only [d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9863 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9876 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23167 q ha hb
    | true =>
      simp only [d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9877 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9878 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9879 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9880 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9881 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23174 (p : Pattern) (ha : d9993 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9992 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9993 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9993, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9993, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23175 (p : Pattern) (ha : d9999 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9994 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23174 q ha hb
    | true =>
      simp only [d9994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9995 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9996 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9997 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9998 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9999 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23176 (p : Pattern) (ha : d100941 p = 1) (hb : d101949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9882 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23172 q ha hb
    | true =>
      simp only [d9882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23173 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d10000 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23175 q ha hb
    | true =>
      simp only [d10000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10001 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101947 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101948 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d101949 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23177 (p : Pattern) (ha : d100941 p = 1) (hb : d101955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d101950 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23176 q ha hb
  have h2 (q : Pattern) (ha : d10017 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23169 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d101951 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d101952 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101953 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101954 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101955 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23178 (p : Pattern) (ha : d100941 p = 1) (hb : d101961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d101956 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23177 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101957 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d101958 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d101959 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101960 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101961 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23179 (p : Pattern) (ha : d10169 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10168 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10169 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10169, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10169, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23180 (p : Pattern) (ha : d10316 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10170 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23179 q ha hb
    | true =>
      simp only [d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10171 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10313 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10314 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10315 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10316 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23181 (p : Pattern) (ha : d10322 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10317 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23180 q ha hb
    | true =>
      simp only [d10317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10318 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10319 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10320 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10321 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10322 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23182 (p : Pattern) (ha : d10147 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10147 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10147, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10147, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23183 (p : Pattern) (ha : d10152 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10151 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10152 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10152, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10152, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23184 (p : Pattern) (ha : d10158 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10148 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23182 q ha hb
    | true =>
      simp only [d10148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10149 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10153 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23183 q ha hb
    | true =>
      simp only [d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10154 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10155 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10156 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10157 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10158 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23185 (p : Pattern) (ha : d10175 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10153 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23183 q ha hb
    | true =>
      simp only [d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10154 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10170 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23179 q ha hb
    | true =>
      simp only [d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10171 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10172 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10173 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10174 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10175 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23186 (p : Pattern) (ha : d10299 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10298 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10299 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10299, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10299, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23187 (p : Pattern) (ha : d10305 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10300 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23186 q ha hb
    | true =>
      simp only [d10300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10301 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10302 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10303 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10304 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10305 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23188 (p : Pattern) (ha : d100941 p = 1) (hb : d101969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10176 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23184 q ha hb
    | true =>
      simp only [d10176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23185 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d10306 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23187 q ha hb
    | true =>
      simp only [d10306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10307 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101967 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101968 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d101969 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23189 (p : Pattern) (ha : d100941 p = 1) (hb : d101975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d101970 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23188 q ha hb
  have h2 (q : Pattern) (ha : d10323 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23181 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d101971 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d101972 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101973 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101974 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101975 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23190 (p : Pattern) (ha : d100941 p = 1) (hb : d101981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d101976 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23189 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101977 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d101978 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d101979 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101980 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101981 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23191 (p : Pattern) (ha : d10446 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10445 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10446 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10446, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10446, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23192 (p : Pattern) (ha : d10582 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10447 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23191 q ha hb
    | true =>
      simp only [d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10448 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10579 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10580 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10581 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10582 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23193 (p : Pattern) (ha : d10588 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10583 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23192 q ha hb
    | true =>
      simp only [d10583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10584 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10585 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10586 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10587 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10588 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23194 (p : Pattern) (ha : d10424 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10423 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10424 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10424, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10424, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23195 (p : Pattern) (ha : d10429 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10428 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10429 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10429, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10429, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23196 (p : Pattern) (ha : d10435 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10425 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23194 q ha hb
    | true =>
      simp only [d10425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10426 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10430 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23195 q ha hb
    | true =>
      simp only [d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10431 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10432 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10433 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10434 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10435 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23197 (p : Pattern) (ha : d10452 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10430 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23195 q ha hb
    | true =>
      simp only [d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10431 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10447 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23191 q ha hb
    | true =>
      simp only [d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10448 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10449 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10450 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10451 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10452 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23198 (p : Pattern) (ha : d10565 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10564 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10565 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10565, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10565, d100941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro23199 (p : Pattern) (ha : d10571 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10566 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23198 q ha hb
    | true =>
      simp only [d10566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10567 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10568 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10569 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10570 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10571 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23200 (p : Pattern) (ha : d100941 p = 1) (hb : d101990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10453 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23196 q ha hb
    | true =>
      simp only [d10453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23197 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d10572 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23199 q ha hb
    | true =>
      simp only [d10572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10573 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101987 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101988 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101989 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d101990 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23201 (p : Pattern) (ha : d100941 p = 1) (hb : d101996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d101991 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23200 q ha hb
  have h2 (q : Pattern) (ha : d10589 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23193 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d101992 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d101993 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101994 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101995 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101996 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23202 (p : Pattern) (ha : d100941 p = 1) (hb : d102002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d101997 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23201 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101998 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d101999 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d102000 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d102000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d102000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d102001 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d102001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d102001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d102002 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d102002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d102002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23203 (p : Pattern) (ha : d100941 p = 1) (hb : d102008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d100941 q = 1) (hb : d101925 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23144 q ha hb
    | true =>
      simp only [d101925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23155 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d101943 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23166 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d101944 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d101962 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23178 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d101963 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d101964 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d101982 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23190 q ha hb
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d101983 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d100941 q = 1) (hb : d101984 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d100941 q = 1) (hb : d101985 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d100941 q = 1) (hb : d102003 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d102003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d102003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23202 q ha hb
  have h12 (q : Pattern) (ha : d100941 q = 1) (hb : d102004 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d102004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d102004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d100941 q = 1) (hb : d102005 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d102005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d102005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d100941 q = 1) (hb : d102006 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d102006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d102006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d100941 q = 1) (hb : d102007 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d102007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d102007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d100941 q = 1) (hb : d102008 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d102008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d102008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro23204 (p : Pattern) (ha : d100941 p = 1) (hb : d102014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d102009 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d102009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23203 q ha hb
    | true =>
      simp only [d102009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d102010 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d102010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d102011 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d102011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d102012 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d102012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d102013 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d102013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d102014 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d102014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23205 (p : Pattern) (ha : d100941 p = 1) (hb : d102020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d102015 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d102015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23204 q ha hb
    | true =>
      simp only [d102015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d102016 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d102016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d102017 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d102017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d102018 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d102018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d102019 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d102019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d102020 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d102020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23206 (p : Pattern) (ha : d100941 p = 1) (hb : d102026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d102021 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d102021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23205 q ha hb
    | true =>
      simp only [d102021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d102022 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d102022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d102023 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d102023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d102024 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d102024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d102025 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d102025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d102026 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d102026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23207 (p : Pattern) (ha : d100941 p = 1) (hb : d102032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d102027 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d102027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23206 q ha hb
    | true =>
      simp only [d102027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d102028 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d102028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d102029 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d102029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d102030 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d102030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d102031 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d102031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d102032 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d102032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23208 (p : Pattern) (ha : d100941 p = 1) (hb : d102038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d102033 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d102033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23207 q ha hb
    | true =>
      simp only [d102033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d102034 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d102035 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d102036 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d102037 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d102038 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23209 (p : Pattern) (ha : d100941 p = 1) (hb : d102044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d102039 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23208 q ha hb
    | true =>
      simp only [d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d102040 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d102041 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d102042 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d102043 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d102044 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23210 (p : Pattern) (ha : d100941 p = 1) (hb : d102050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d102045 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23209 q ha hb
    | true =>
      simp only [d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d102046 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d102047 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d102048 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d102049 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d102050 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23211 (p : Pattern) (ha : d100941 p = 1) (hb : d129477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9437 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23138 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129473 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129474 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129475 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129476 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129477 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23212 (p : Pattern) (ha : d100941 p = 1) (hb : d129487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9342 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23135 q ha hb
    | true =>
      simp only [d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23131 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129483 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129484 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129485 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129486 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23213 (p : Pattern) (ha : d100941 p = 1) (hb : d129493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129488 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23212 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129489 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129490 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129491 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23214 (p : Pattern) (ha : d100941 p = 1) (hb : d129499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129478 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23211 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129479 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129480 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129481 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129482 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129494 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23213 q ha hb
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d129495 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d129496 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d100941 q = 1) (hb : d129497 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d100941 q = 1) (hb : d129498 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d100941 q = 1) (hb : d129499 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23215 (p : Pattern) (ha : d100941 p = 1) (hb : d129505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129500 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23151 q hb ha
    | true =>
      simp only [d129500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23146 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129501 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129502 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129503 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129504 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129505 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23216 (p : Pattern) (ha : d100941 p = 1) (hb : d129511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129506 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23215 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129507 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129508 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129509 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129510 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129511 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23217 (p : Pattern) (ha : d100941 p = 1) (hb : d129517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129512 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23216 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129513 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129514 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129515 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129516 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129517 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23218 (p : Pattern) (ha : d100941 p = 1) (hb : d129524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129519 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23162 q hb ha
    | true =>
      simp only [d129519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23157 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129520 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129521 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129522 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129523 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129524 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23219 (p : Pattern) (ha : d100941 p = 1) (hb : d129530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129525 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23218 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129526 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129527 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129528 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129529 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129530 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23220 (p : Pattern) (ha : d100941 p = 1) (hb : d129536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129531 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23219 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129532 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129533 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129534 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129535 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129536 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23221 (p : Pattern) (ha : d100941 p = 1) (hb : d129540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129540 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d100941, d129540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100941, d129540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro23222 (p : Pattern) (ha : d100941 p = 1) (hb : d129546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129541 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23221 q ha hb
    | true =>
      simp only [d129541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129542 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9876 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23167 q ha hb
    | true =>
      simp only [d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9877 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129543 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129544 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d129545 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d129546 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23223 (p : Pattern) (ha : d100941 p = 1) (hb : d129552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23222 q ha hb
    | true =>
      simp only [d129547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23168 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23224 (p : Pattern) (ha : d100941 p = 1) (hb : d129558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129553 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23223 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129554 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129555 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129556 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129557 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129558 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23225 (p : Pattern) (ha : d100941 p = 1) (hb : d129564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129559 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23224 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129560 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129561 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129562 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129563 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129564 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23226 (p : Pattern) (ha : d100941 p = 1) (hb : d129569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129568 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129569 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d100941, d129569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100941, d129569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro23227 (p : Pattern) (ha : d100941 p = 1) (hb : d129575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129570 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23226 q ha hb
    | true =>
      simp only [d129570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129571 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10170 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23179 q ha hb
    | true =>
      simp only [d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10171 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129572 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129573 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d129574 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d129575 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23228 (p : Pattern) (ha : d100941 p = 1) (hb : d129581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129576 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23227 q ha hb
    | true =>
      simp only [d129576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23180 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23229 (p : Pattern) (ha : d100941 p = 1) (hb : d129587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23228 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129586 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129587 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23230 (p : Pattern) (ha : d100941 p = 1) (hb : d129593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129588 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23229 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129589 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129590 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129591 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129592 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129593 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23231 (p : Pattern) (ha : d100941 p = 1) (hb : d129599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129598 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129599 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d100941, d129599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100941, d129599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro23232 (p : Pattern) (ha : d100941 p = 1) (hb : d129605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23231 q ha hb
    | true =>
      simp only [d129600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10447 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23191 q ha hb
    | true =>
      simp only [d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10448 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d129604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d129605 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro23233 (p : Pattern) (ha : d100941 p = 1) (hb : d129611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23232 q ha hb
    | true =>
      simp only [d129606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23192 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23234 (p : Pattern) (ha : d100941 p = 1) (hb : d129617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23233 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129616 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129617 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23235 (p : Pattern) (ha : d100941 p = 1) (hb : d129623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129618 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23234 q ha hb
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129619 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129620 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129621 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129622 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129623 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23236 (p : Pattern) (ha : d100941 p = 1) (hb : d129629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d100941 q = 1) (hb : d129518 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23214 q ha hb
    | true =>
      simp only [d129518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23217 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129537 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23220 q ha hb
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129538 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129565 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23225 q ha hb
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129566 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129567 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d100941 q = 1) (hb : d129594 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23230 q ha hb
  have h8 (q : Pattern) (ha : d100941 q = 1) (hb : d129595 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d100941 q = 1) (hb : d129596 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d100941 q = 1) (hb : d129597 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d100941 q = 1) (hb : d129624 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23235 q ha hb
  have h12 (q : Pattern) (ha : d100941 q = 1) (hb : d129625 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d100941 q = 1) (hb : d129626 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d100941 q = 1) (hb : d129627 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d100941 q = 1) (hb : d129628 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d100941 q = 1) (hb : d129629 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro23237 (p : Pattern) (ha : d100941 p = 1) (hb : d129635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129630 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23236 q ha hb
    | true =>
      simp only [d129630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129631 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129632 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129633 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129634 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129635 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23238 (p : Pattern) (ha : d100941 p = 1) (hb : d129641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129636 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23237 q ha hb
    | true =>
      simp only [d129636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129637 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129638 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129639 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129640 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129641 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23239 (p : Pattern) (ha : d100941 p = 1) (hb : d129647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129642 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23238 q ha hb
    | true =>
      simp only [d129642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129643 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129644 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129645 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129646 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129647 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23240 (p : Pattern) (ha : d100941 p = 1) (hb : d129653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129648 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23239 q ha hb
    | true =>
      simp only [d129648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129649 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129650 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129651 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129652 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129653 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23241 (p : Pattern) (ha : d100941 p = 1) (hb : d129659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129654 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23240 q ha hb
    | true =>
      simp only [d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129655 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129656 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129657 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129658 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129659 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23242 (p : Pattern) (ha : d100941 p = 1) (hb : d129665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129660 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23241 q ha hb
    | true =>
      simp only [d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129661 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129662 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129663 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129664 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129665 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23243 (p : Pattern) (ha : d100941 p = 1) (hb : d129671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129666 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23242 q ha hb
    | true =>
      simp only [d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100941 q = 1) (hb : d129667 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100941 q = 1) (hb : d129668 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100941 q = 1) (hb : d129669 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100941 q = 1) (hb : d129670 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100941 q = 1) (hb : d129671 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23244 (p : Pattern) (ha : d82381 p = 1) (hb : d102050 p = 1) : d102050 p = 1 := by
  have h0 (q : Pattern) (ha : d82381 q = 1) (hb : d102050 q = 1) : d102050 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro23245 (p : Pattern) (ha : d1 p = 1) (hb : d102050 p = 1) : d102050 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d102050 q = 1) : d102050 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro23246 (p : Pattern) (ha : d82381 p = 1) (hb : d129671 p = 1) : d129671 p = 1 := by
  have h0 (q : Pattern) (ha : d82381 q = 1) (hb : d129671 q = 1) : d129671 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro23247 (p : Pattern) (ha : d1 p = 1) (hb : d129671 p = 1) : d129671 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d129671 q = 1) : d129671 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro23248 (p : Pattern) (ha : d0 p = 1) (hb : d129671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129671 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro23249 (p : Pattern) (ha : d102050 p = 1) (hb : d129672 p = 1) : d102050 p = 1 := by
  have h0 (q : Pattern) (ha : d102050 q = 1) (hb : d129672 q = 1) : d102050 q = 1 := by
    exact ha
  exact h0 p ha hb
end NetHack.Soko22Hazard87
