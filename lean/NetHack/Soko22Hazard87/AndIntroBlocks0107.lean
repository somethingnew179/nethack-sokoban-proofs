import NetHack.Soko22Hazard87.AndIntroBlocks0106
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro26750 (p : Pattern) (ha : d144595 p = 1) (hb : d145623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144432 q = 1) (hb : d145484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144432, d145484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144432, d145484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26718 q ha hb
  have h2 (q : Pattern) (ha : d144433 q = 1) (hb : d145485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144433, d145485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144433, d145485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d144442 q = 1) (hb : d145493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144442, d145493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26718 q ha hb
    | true =>
      simp only [d144442, d145493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26720 q ha hb
  have h4 (q : Pattern) (ha : d144443 q = 1) (hb : d145494 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144443, d145494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144443, d145494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144444 q = 1) (hb : d145495 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144444, d145495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144444, d145495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144507 q = 1) (hb : d145561 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144507, d145561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26731 q ha hb
    | true =>
      simp only [d144507, d145561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26738 q ha hb
  have h7 (q : Pattern) (ha : d144520 q = 1) (hb : d145563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144520, d145563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26739 q ha hb
    | true =>
      simp only [d144520, d145563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26710 q hb ha
  have h8 (q : Pattern) (ha : d144521 q = 1) (hb : d145564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144521, d145564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144521, d145564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144522 q = 1) (hb : d145565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144522, d145565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144522, d145565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144523 q = 1) (hb : d145566 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144523, d145566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144523, d145566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144527 q = 1) (hb : d145570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144527, d145570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144527, d145570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26740 q ha hb
  have h12 (q : Pattern) (ha : d120535 q = 1) (hb : d144529 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120535, d144529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120535, d144529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26711 q ha hb
  have h13 (q : Pattern) (ha : d144530 q = 1) (hb : d145571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144530, d145571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144530, d145571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d144531 q = 1) (hb : d145572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144531, d145572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144531, d145572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d144532 q = 1) (hb : d145573 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144532, d145573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d144532, d145573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d144533 q = 1) (hb : d145574 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144533, d145574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144533, d145574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d144583 q = 1) (hb : d145618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144583, d145618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144583, d145618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26749 q ha hb
  have h18 (q : Pattern) (ha : d120601 q = 1) (hb : d144590 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120601, d144590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120601, d144590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26715 q ha hb
  have h19 (q : Pattern) (ha : d144591 q = 1) (hb : d145619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144591, d145619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d144591, d145619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d144592 q = 1) (hb : d145620 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144592, d145620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d144592, d145620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d144593 q = 1) (hb : d145621 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144593, d145621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d144593, d145621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d144594 q = 1) (hb : d145622 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144594, d145622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d144594, d145622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d144595 q = 1) (hb : d145623 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d144595, d145623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d144595, d145623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26751 (p : Pattern) (ha : d144601 p = 1) (hb : d145629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144596 q = 1) (hb : d145624 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d144596, d145624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144596, d145624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26750 q ha hb
  have h2 (q : Pattern) (ha : d144597 q = 1) (hb : d145625 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d144597, d145625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144597, d145625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144598 q = 1) (hb : d145626 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d144598, d145626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144598, d145626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144599 q = 1) (hb : d145627 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d144599, d145627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144599, d145627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144600 q = 1) (hb : d145628 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d144600, d145628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144600, d145628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144601 q = 1) (hb : d145629 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d144601, d145629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144601, d145629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26752 (p : Pattern) (ha : d52694 p = 1) (hb : d145632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1112 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1113 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d14762 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52694 q = 1) (hb : d145632 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26753 (p : Pattern) (ha : d52705 p = 1) (hb : d145636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1123 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1124 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1127 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52705 q = 1) (hb : d145636 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26754 (p : Pattern) (ha : d144613 p = 1) (hb : d145643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144604 q = 1) (hb : d145633 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144604, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26752 q ha hb
    | true =>
      simp only [d144604, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144605 q = 1) (hb : d145634 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144605, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144605, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144606 q = 1) (hb : d145635 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144606, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144606, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144607 q = 1) (hb : d145637 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144607, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26753 q ha hb
    | true =>
      simp only [d144607, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144608 q = 1) (hb : d145638 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144608, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144608, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144609 q = 1) (hb : d145639 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144609, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144609, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144610 q = 1) (hb : d145640 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144610, d145640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144610, d145640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144611 q = 1) (hb : d145641 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144611, d145641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144611, d145641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144612 q = 1) (hb : d145642 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144612, d145642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144612, d145642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144613 q = 1) (hb : d145643 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144613, d145643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144613, d145643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro26755 (p : Pattern) (ha : d144617 p = 1) (hb : d145647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144607 q = 1) (hb : d145637 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144607, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26753 q ha hb
    | true =>
      simp only [d144607, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144608 q = 1) (hb : d145638 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144608, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144608, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144609 q = 1) (hb : d145639 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144609, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144609, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144611 q = 1) (hb : d145641 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144611, d145641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144611, d145641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144616 q = 1) (hb : d145646 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144616, d145646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144616, d145646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144617 q = 1) (hb : d145647 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144617, d145647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144617, d145647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26756 (p : Pattern) (ha : d144623 p = 1) (hb : d145653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144614 q = 1) (hb : d145644 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26754 q ha hb
    | true =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144615 q = 1) (hb : d145645 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144618 q = 1) (hb : d145648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26755 q ha hb
    | true =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144619 q = 1) (hb : d145649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144620 q = 1) (hb : d145650 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144620, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144620, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144621 q = 1) (hb : d145651 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144621, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144621, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144622 q = 1) (hb : d145652 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144622, d145652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144622, d145652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144623 q = 1) (hb : d145653 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144623, d145653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144623, d145653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26757 (p : Pattern) (ha : d144627 p = 1) (hb : d145657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144618 q = 1) (hb : d145648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26755 q ha hb
    | true =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144619 q = 1) (hb : d145649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144624 q = 1) (hb : d145654 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144624, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144624, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144625 q = 1) (hb : d145655 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144625, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144625, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144626 q = 1) (hb : d145656 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144626, d145656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144626, d145656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144627 q = 1) (hb : d145657 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144627, d145657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144627, d145657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26758 (p : Pattern) (ha : d144633 p = 1) (hb : d145663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144628 q = 1) (hb : d145658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144628, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26756 q ha hb
    | true =>
      simp only [d144628, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26757 q ha hb
  have h2 (q : Pattern) (ha : d144629 q = 1) (hb : d145659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144629, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144629, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144630 q = 1) (hb : d145660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144630, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144630, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144631 q = 1) (hb : d145661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144631, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144631, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144632 q = 1) (hb : d145662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144632, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144632, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144633 q = 1) (hb : d145663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144633, d145663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144633, d145663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26759 (p : Pattern) (ha : d144636 p = 1) (hb : d145666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144614 q = 1) (hb : d145644 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26754 q ha hb
    | true =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144615 q = 1) (hb : d145645 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144618 q = 1) (hb : d145648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26755 q ha hb
    | true =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144619 q = 1) (hb : d145649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144620 q = 1) (hb : d145650 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144620, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144620, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144621 q = 1) (hb : d145651 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144621, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144621, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144622 q = 1) (hb : d145652 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144622, d145652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144622, d145652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144636 q = 1) (hb : d145666 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144636, d145666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144636, d145666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26760 (p : Pattern) (ha : d144637 p = 1) (hb : d145667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144618 q = 1) (hb : d145648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26755 q ha hb
    | true =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144619 q = 1) (hb : d145649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144624 q = 1) (hb : d145654 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144624, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144624, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144625 q = 1) (hb : d145655 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144625, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144625, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144626 q = 1) (hb : d145656 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144626, d145656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144626, d145656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144637 q = 1) (hb : d145667 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144637, d145667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144637, d145667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26761 (p : Pattern) (ha : d144643 p = 1) (hb : d145673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144628 q = 1) (hb : d145658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144628, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26756 q ha hb
    | true =>
      simp only [d144628, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26757 q ha hb
  have h2 (q : Pattern) (ha : d144629 q = 1) (hb : d145659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144629, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144629, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144630 q = 1) (hb : d145660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144630, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144630, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144631 q = 1) (hb : d145661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144631, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144631, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144632 q = 1) (hb : d145662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144632, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144632, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144638 q = 1) (hb : d145668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144638, d145668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26759 q ha hb
    | true =>
      simp only [d144638, d145668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26760 q ha hb
  have h7 (q : Pattern) (ha : d144639 q = 1) (hb : d145669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144639, d145669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144639, d145669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144640 q = 1) (hb : d145670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144640, d145670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144640, d145670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144641 q = 1) (hb : d145671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144641, d145671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144641, d145671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144642 q = 1) (hb : d145672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144642, d145672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144642, d145672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144643 q = 1) (hb : d145673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144643, d145673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144643, d145673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26762 (p : Pattern) (ha : d144648 p = 1) (hb : d145678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144614 q = 1) (hb : d145644 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26754 q ha hb
    | true =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144615 q = 1) (hb : d145645 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144618 q = 1) (hb : d145648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26755 q ha hb
    | true =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144619 q = 1) (hb : d145649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144620 q = 1) (hb : d145650 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144620, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144620, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144621 q = 1) (hb : d145651 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144621, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144621, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144647 q = 1) (hb : d145677 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144647, d145677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144647, d145677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144648 q = 1) (hb : d145678 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144648, d145678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144648, d145678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26763 (p : Pattern) (ha : d144650 p = 1) (hb : d145680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144618 q = 1) (hb : d145648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26755 q ha hb
    | true =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144619 q = 1) (hb : d145649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144624 q = 1) (hb : d145654 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144624, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144624, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144625 q = 1) (hb : d145655 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144625, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144625, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144649 q = 1) (hb : d145679 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144649, d145679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144649, d145679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144650 q = 1) (hb : d145680 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144650, d145680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144650, d145680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26764 (p : Pattern) (ha : d144657 p = 1) (hb : d145687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144614 q = 1) (hb : d145644 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26754 q ha hb
    | true =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144615 q = 1) (hb : d145645 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144618 q = 1) (hb : d145648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26755 q ha hb
    | true =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144619 q = 1) (hb : d145649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144620 q = 1) (hb : d145650 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144620, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144620, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144655 q = 1) (hb : d145685 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144655, d145685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144655, d145685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144656 q = 1) (hb : d145686 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144656, d145686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144656, d145686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144657 q = 1) (hb : d145687 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144657, d145687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144657, d145687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26765 (p : Pattern) (ha : d144660 p = 1) (hb : d145690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144618 q = 1) (hb : d145648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26755 q ha hb
    | true =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144619 q = 1) (hb : d145649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144624 q = 1) (hb : d145654 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144624, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144624, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144658 q = 1) (hb : d145688 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144658, d145688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144658, d145688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144659 q = 1) (hb : d145689 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144659, d145689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144659, d145689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144660 q = 1) (hb : d145690 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144660, d145690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144660, d145690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26766 (p : Pattern) (ha : d52684 p = 1) (hb : d145694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1102 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1103 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d14757 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52684 q = 1) (hb : d145694 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26767 (p : Pattern) (ha : d144672 p = 1) (hb : d145700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144664 q = 1) (hb : d145695 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144664, d145695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26766 q ha hb
    | true =>
      simp only [d144664, d145695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144665 q = 1) (hb : d145696 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144665, d145696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144665, d145696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144666 q = 1) (hb : d145697 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144666, d145697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144666, d145697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113358 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d144667 q = 1) (hb : d145633 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144667, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26752 q ha hb
    | true =>
      simp only [d144667, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144668 q = 1) (hb : d145634 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144668, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144668, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144669 q = 1) (hb : d145635 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144669, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144669, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144670 q = 1) (hb : d145698 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144670, d145698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144670, d145698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d144604 q = 1) (hb : d145633 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144604, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26752 q ha hb
    | true =>
      simp only [d144604, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d144605 q = 1) (hb : d145634 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144605, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144605, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d144606 q = 1) (hb : d145635 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144606, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144606, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144607 q = 1) (hb : d145637 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144607, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26753 q ha hb
    | true =>
      simp only [d144607, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d144608 q = 1) (hb : d145638 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144608, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144608, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144609 q = 1) (hb : d145639 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144609, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144609, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d144610 q = 1) (hb : d145640 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144610, d145640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144610, d145640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d144671 q = 1) (hb : d145699 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144671, d145699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144671, d145699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d144672 q = 1) (hb : d145700 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144672, d145700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d144672, d145700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h19 p ha hb
theorem andIntro26768 (p : Pattern) (ha : d144678 p = 1) (hb : d145706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144673 q = 1) (hb : d145701 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144673, d145701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26767 q ha hb
    | true =>
      simp only [d144673, d145701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144674 q = 1) (hb : d145702 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144674, d145702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144674, d145702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144614 q = 1) (hb : d145644 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26754 q ha hb
    | true =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144615 q = 1) (hb : d145645 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144675 q = 1) (hb : d145703 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144675, d145703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144675, d145703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144676 q = 1) (hb : d145704 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144676, d145704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144676, d145704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144677 q = 1) (hb : d145705 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144677, d145705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144677, d145705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144678 q = 1) (hb : d145706 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144678, d145706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144678, d145706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26769 (p : Pattern) (ha : d52705 p = 1) (hb : d145709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5540 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15036 q ha hb
    | true =>
      simp only [d5540, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5541 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5541, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d5542 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5542, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5542, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5543 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5543, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5543, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5544 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52705 q = 1) (hb : d145709 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26770 (p : Pattern) (ha : d144613 p = 1) (hb : d145715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144604 q = 1) (hb : d145633 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144604, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26752 q ha hb
    | true =>
      simp only [d144604, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144605 q = 1) (hb : d145634 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144605, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144605, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144606 q = 1) (hb : d145635 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144606, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144606, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144607 q = 1) (hb : d145637 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144607, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26753 q ha hb
    | true =>
      simp only [d144607, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144608 q = 1) (hb : d145638 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144608, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144608, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144609 q = 1) (hb : d145639 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144609, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144609, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144610 q = 1) (hb : d145640 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144610, d145640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144610, d145640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144607 q = 1) (hb : d145710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144607, d145710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26769 q ha hb
    | true =>
      simp only [d144607, d145710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144608 q = 1) (hb : d145711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144608, d145711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144608, d145711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144609 q = 1) (hb : d145712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144609, d145712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144609, d145712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d144611 q = 1) (hb : d145713 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144611, d145713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144611, d145713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144612 q = 1) (hb : d145714 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144612, d145714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144612, d145714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144613 q = 1) (hb : d145715 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144613, d145715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144613, d145715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro26771 (p : Pattern) (ha : d144684 p = 1) (hb : d145721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144614 q = 1) (hb : d145716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144614, d145716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26770 q ha hb
    | true =>
      simp only [d144614, d145716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144615 q = 1) (hb : d145717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144615, d145717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144615, d145717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144681 q = 1) (hb : d145718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144681, d145718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144681, d145718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144682 q = 1) (hb : d145719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144682, d145719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144682, d145719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144683 q = 1) (hb : d145720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144683, d145720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144683, d145720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144684 q = 1) (hb : d145721 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144684, d145721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144684, d145721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26772 (p : Pattern) (ha : d144690 p = 1) (hb : d145727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144651 q = 1) (hb : d145681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144651, d145681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26762 q ha hb
    | true =>
      simp only [d144651, d145681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26763 q ha hb
  have h2 (q : Pattern) (ha : d144652 q = 1) (hb : d145682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144652, d145682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144652, d145682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144653 q = 1) (hb : d145683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144653, d145683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144653, d145683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144654 q = 1) (hb : d145684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144654, d145684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144654, d145684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144661 q = 1) (hb : d145691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144661, d145691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26764 q ha hb
    | true =>
      simp only [d144661, d145691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26765 q ha hb
  have h6 (q : Pattern) (ha : d144662 q = 1) (hb : d145692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144662, d145692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144662, d145692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144663 q = 1) (hb : d145693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144663, d145693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144663, d145693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144679 q = 1) (hb : d145707 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144679, d145707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26768 q ha hb
    | true =>
      simp only [d144679, d145707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26756 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144628 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d144680 q = 1) (hb : d145708 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144680, d145708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144680, d145708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d144685 q = 1) (hb : d145722 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144685, d145722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26771 q ha hb
    | true =>
      simp only [d144685, d145722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d144686 q = 1) (hb : d145723 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144686, d145723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144686, d145723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144687 q = 1) (hb : d145724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144687, d145724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144687, d145724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144688 q = 1) (hb : d145725 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144688, d145725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144688, d145725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144689 q = 1) (hb : d145726 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144689, d145726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144689, d145726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144690 q = 1) (hb : d145727 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144690, d145727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144690, d145727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro26773 (p : Pattern) (ha : d144691 p = 1) (hb : d145728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144614 q = 1) (hb : d145644 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26754 q ha hb
    | true =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144615 q = 1) (hb : d145645 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144618 q = 1) (hb : d145648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26755 q ha hb
    | true =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144619 q = 1) (hb : d145649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144620 q = 1) (hb : d145650 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144620, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144620, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144621 q = 1) (hb : d145651 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144621, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144621, d145651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144647 q = 1) (hb : d145677 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144647, d145677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144647, d145677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144691 q = 1) (hb : d145728 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144691, d145728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144691, d145728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26774 (p : Pattern) (ha : d144692 p = 1) (hb : d145729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144618 q = 1) (hb : d145648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26755 q ha hb
    | true =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144619 q = 1) (hb : d145649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144624 q = 1) (hb : d145654 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144624, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144624, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144625 q = 1) (hb : d145655 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144625, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144625, d145655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144649 q = 1) (hb : d145679 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144649, d145679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144649, d145679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144692 q = 1) (hb : d145729 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144692, d145729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144692, d145729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26775 (p : Pattern) (ha : d144697 p = 1) (hb : d145734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144614 q = 1) (hb : d145644 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26754 q ha hb
    | true =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144615 q = 1) (hb : d145645 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144618 q = 1) (hb : d145648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26755 q ha hb
    | true =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144619 q = 1) (hb : d145649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144620 q = 1) (hb : d145650 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144620, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144620, d145650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144655 q = 1) (hb : d145685 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144655, d145685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144655, d145685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144656 q = 1) (hb : d145686 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144656, d145686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144656, d145686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144697 q = 1) (hb : d145734 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144697, d145734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144697, d145734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26776 (p : Pattern) (ha : d144698 p = 1) (hb : d145735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144618 q = 1) (hb : d145648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26755 q ha hb
    | true =>
      simp only [d144618, d145648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144619 q = 1) (hb : d145649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144619, d145649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144624 q = 1) (hb : d145654 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144624, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144624, d145654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144658 q = 1) (hb : d145688 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144658, d145688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144658, d145688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144659 q = 1) (hb : d145689 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144659, d145689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144659, d145689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144698 q = 1) (hb : d145735 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144698, d145735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144698, d145735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26777 (p : Pattern) (ha : d144702 p = 1) (hb : d145739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144673 q = 1) (hb : d145701 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144673, d145701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26767 q ha hb
    | true =>
      simp only [d144673, d145701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144674 q = 1) (hb : d145702 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144674, d145702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144674, d145702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144614 q = 1) (hb : d145644 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26754 q ha hb
    | true =>
      simp only [d144614, d145644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144615 q = 1) (hb : d145645 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144615, d145645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144675 q = 1) (hb : d145703 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144675, d145703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144675, d145703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144676 q = 1) (hb : d145704 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144676, d145704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144676, d145704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144677 q = 1) (hb : d145705 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144677, d145705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144677, d145705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144702 q = 1) (hb : d145739 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144702, d145739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144702, d145739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26778 (p : Pattern) (ha : d144705 p = 1) (hb : d145742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144614 q = 1) (hb : d145716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144614, d145716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26770 q ha hb
    | true =>
      simp only [d144614, d145716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144615 q = 1) (hb : d145717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144615, d145717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144615, d145717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144681 q = 1) (hb : d145718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144681, d145718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144681, d145718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144682 q = 1) (hb : d145719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144682, d145719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144682, d145719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144683 q = 1) (hb : d145720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144683, d145720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144683, d145720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144705 q = 1) (hb : d145742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144705, d145742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144705, d145742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26779 (p : Pattern) (ha : d144711 p = 1) (hb : d145748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144651 q = 1) (hb : d145681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144651, d145681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26762 q ha hb
    | true =>
      simp only [d144651, d145681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26763 q ha hb
  have h2 (q : Pattern) (ha : d144652 q = 1) (hb : d145682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144652, d145682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144652, d145682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144653 q = 1) (hb : d145683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144653, d145683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144653, d145683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144654 q = 1) (hb : d145684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144654, d145684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144654, d145684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144661 q = 1) (hb : d145691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144661, d145691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26764 q ha hb
    | true =>
      simp only [d144661, d145691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26765 q ha hb
  have h6 (q : Pattern) (ha : d144662 q = 1) (hb : d145692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144662, d145692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144662, d145692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144663 q = 1) (hb : d145693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144663, d145693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144663, d145693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144679 q = 1) (hb : d145707 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144679, d145707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26768 q ha hb
    | true =>
      simp only [d144679, d145707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26756 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144628 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d144680 q = 1) (hb : d145708 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144680, d145708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144680, d145708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d144685 q = 1) (hb : d145722 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144685, d145722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26771 q ha hb
    | true =>
      simp only [d144685, d145722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d144686 q = 1) (hb : d145723 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144686, d145723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144686, d145723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144687 q = 1) (hb : d145724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144687, d145724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144687, d145724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144688 q = 1) (hb : d145725 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144688, d145725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144688, d145725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144689 q = 1) (hb : d145726 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144689, d145726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144689, d145726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144693 q = 1) (hb : d145730 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144693, d145730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26773 q ha hb
    | true =>
      simp only [d144693, d145730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26774 q ha hb
  have h17 (q : Pattern) (ha : d144694 q = 1) (hb : d145731 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144694, d145731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144694, d145731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d144695 q = 1) (hb : d145732 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144695, d145732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d144695, d145732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d144696 q = 1) (hb : d145733 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144696, d145733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144696, d145733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d144699 q = 1) (hb : d145736 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144699, d145736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26775 q ha hb
    | true =>
      simp only [d144699, d145736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26776 q ha hb
  have h21 (q : Pattern) (ha : d144700 q = 1) (hb : d145737 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144700, d145737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144700, d145737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d144701 q = 1) (hb : d145738 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144701, d145738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d144701, d145738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d144703 q = 1) (hb : d145740 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144703, d145740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26777 q ha hb
    | true =>
      simp only [d144703, d145740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26759 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d144638 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d144704 q = 1) (hb : d145741 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144704, d145741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d144704, d145741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d144706 q = 1) (hb : d145743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144706, d145743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26778 q ha hb
    | true =>
      simp only [d144706, d145743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d144707 q = 1) (hb : d145744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144707, d145744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d144707, d145744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d144708 q = 1) (hb : d145745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144708, d145745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d144708, d145745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d144709 q = 1) (hb : d145746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144709, d145746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d144709, d145746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d144710 q = 1) (hb : d145747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144710, d145747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d144710, d145747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d144711 q = 1) (hb : d145748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144711, d145748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d144711, d145748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro26780 (p : Pattern) (ha : d144718 p = 1) (hb : d145755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144628 q = 1) (hb : d145658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144628, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26756 q ha hb
    | true =>
      simp only [d144628, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26757 q ha hb
  have h2 (q : Pattern) (ha : d144629 q = 1) (hb : d145659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144629, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144629, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144630 q = 1) (hb : d145660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144630, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144630, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144631 q = 1) (hb : d145661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144631, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144631, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144632 q = 1) (hb : d145662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144632, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144632, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144713 q = 1) (hb : d145750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144713, d145750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26757 q ha hb
    | true =>
      simp only [d144713, d145750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144714 q = 1) (hb : d145751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144714, d145751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144714, d145751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144715 q = 1) (hb : d145752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144715, d145752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144715, d145752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144716 q = 1) (hb : d145753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144716, d145753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144716, d145753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144717 q = 1) (hb : d145754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144717, d145754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144717, d145754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144718 q = 1) (hb : d145755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144718, d145755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144718, d145755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26781 (p : Pattern) (ha : d144724 p = 1) (hb : d145761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144713 q = 1) (hb : d145750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144713, d145750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26757 q ha hb
    | true =>
      simp only [d144713, d145750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144714 q = 1) (hb : d145751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144714, d145751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144714, d145751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144715 q = 1) (hb : d145752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144715, d145752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144715, d145752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144716 q = 1) (hb : d145753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144716, d145753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144716, d145753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144717 q = 1) (hb : d145754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144717, d145754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144717, d145754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144719 q = 1) (hb : d145756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144719, d145756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26760 q ha hb
    | true =>
      simp only [d144719, d145756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144720 q = 1) (hb : d145757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144720, d145757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144720, d145757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144721 q = 1) (hb : d145758 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144721, d145758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144721, d145758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144722 q = 1) (hb : d145759 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144722, d145759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144722, d145759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144723 q = 1) (hb : d145760 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144723, d145760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144723, d145760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144724 q = 1) (hb : d145761 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144724, d145761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144724, d145761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26782 (p : Pattern) (ha : d144731 p = 1) (hb : d145768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144703 q = 1) (hb : d145740 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144703, d145740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26777 q ha hb
    | true =>
      simp only [d144703, d145740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26759 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144638 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144704 q = 1) (hb : d145741 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144704, d145741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144704, d145741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d144706 q = 1) (hb : d145743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144706, d145743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26778 q ha hb
    | true =>
      simp only [d144706, d145743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144707 q = 1) (hb : d145744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144707, d145744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144707, d145744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144708 q = 1) (hb : d145745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144708, d145745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144708, d145745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144729 q = 1) (hb : d145766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144729, d145766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144729, d145766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144730 q = 1) (hb : d145767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144730, d145767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144730, d145767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144731 q = 1) (hb : d145768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144731, d145768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144731, d145768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26783 (p : Pattern) (ha : d144733 p = 1) (hb : d145770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144719 q = 1) (hb : d145756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144719, d145756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26760 q ha hb
    | true =>
      simp only [d144719, d145756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144720 q = 1) (hb : d145757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144720, d145757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144720, d145757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144721 q = 1) (hb : d145758 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144721, d145758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144721, d145758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144722 q = 1) (hb : d145759 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144722, d145759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144722, d145759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144723 q = 1) (hb : d145760 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144723, d145760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144723, d145760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144733 q = 1) (hb : d145770 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144733, d145770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144733, d145770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26784 (p : Pattern) (ha : d52871 p = 1) (hb : d145776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1380 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
  have h3 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1381 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1382 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1383 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d14993 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52871 q = 1) (hb : d145776 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26785 (p : Pattern) (ha : d52876 p = 1) (hb : d145780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1385 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
  have h3 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1386 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1387 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1388 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d15014 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52876 q = 1) (hb : d145780 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26786 (p : Pattern) (ha : d52882 p = 1) (hb : d145785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h3 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1392 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1393 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1394 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1400 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52882 q = 1) (hb : d145785 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26787 (p : Pattern) (ha : d144754 p = 1) (hb : d145791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144739 q = 1) (hb : d145777 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144739, d145777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26784 q ha hb
    | true =>
      simp only [d144739, d145777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144740 q = 1) (hb : d145778 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144740, d145778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144740, d145778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144741 q = 1) (hb : d145779 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144741, d145779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144741, d145779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113459 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d144742 q = 1) (hb : d145781 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144742, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26785 q ha hb
    | true =>
      simp only [d144742, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144743 q = 1) (hb : d145782 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144743, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144743, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144744 q = 1) (hb : d145783 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144744, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144744, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144745 q = 1) (hb : d145784 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144745, d145784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144745, d145784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d144746 q = 1) (hb : d145781 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144746, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26785 q ha hb
    | true =>
      simp only [d144746, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d144747 q = 1) (hb : d145782 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144747, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144747, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d144748 q = 1) (hb : d145783 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144748, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144748, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144749 q = 1) (hb : d145786 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144749, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26786 q ha hb
    | true =>
      simp only [d144749, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d144750 q = 1) (hb : d145787 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144750, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144750, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144751 q = 1) (hb : d145788 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144751, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144751, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d144752 q = 1) (hb : d145789 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144752, d145789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144752, d145789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d144753 q = 1) (hb : d145790 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144753, d145790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144753, d145790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d144754 q = 1) (hb : d145791 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144754, d145791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d144754, d145791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h19 p ha hb
theorem andIntro26788 (p : Pattern) (ha : d144759 p = 1) (hb : d145796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144746 q = 1) (hb : d145781 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144746, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26785 q ha hb
    | true =>
      simp only [d144746, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144747 q = 1) (hb : d145782 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144747, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144747, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144748 q = 1) (hb : d145783 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144748, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144748, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144749 q = 1) (hb : d145786 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144749, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26786 q ha hb
    | true =>
      simp only [d144749, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144750 q = 1) (hb : d145787 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144750, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144750, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144751 q = 1) (hb : d145788 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144751, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144751, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144752 q = 1) (hb : d145789 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144752, d145789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144752, d145789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144757 q = 1) (hb : d145794 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144757, d145794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144757, d145794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144758 q = 1) (hb : d145795 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144758, d145795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144758, d145795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144759 q = 1) (hb : d145796 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144759, d145796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144759, d145796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro26789 (p : Pattern) (ha : d144765 p = 1) (hb : d145802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144755 q = 1) (hb : d145792 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144755, d145792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26787 q ha hb
    | true =>
      simp only [d144755, d145792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144756 q = 1) (hb : d145793 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144756, d145793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144756, d145793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144760 q = 1) (hb : d145797 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144760, d145797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26788 q ha hb
    | true =>
      simp only [d144760, d145797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144761 q = 1) (hb : d145798 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144761, d145798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144761, d145798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144762 q = 1) (hb : d145799 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144762, d145799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144762, d145799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144763 q = 1) (hb : d145800 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144763, d145800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144763, d145800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144764 q = 1) (hb : d145801 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144764, d145801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144764, d145801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144765 q = 1) (hb : d145802 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144765, d145802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144765, d145802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26790 (p : Pattern) (ha : d144767 p = 1) (hb : d145804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144749 q = 1) (hb : d145786 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144749, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26786 q ha hb
    | true =>
      simp only [d144749, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144750 q = 1) (hb : d145787 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144750, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144750, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144751 q = 1) (hb : d145788 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144751, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144751, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144757 q = 1) (hb : d145794 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144757, d145794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144757, d145794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144766 q = 1) (hb : d145803 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144766, d145803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144766, d145803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144767 q = 1) (hb : d145804 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144767, d145804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144767, d145804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26791 (p : Pattern) (ha : d144773 p = 1) (hb : d145810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144760 q = 1) (hb : d145797 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144760, d145797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26788 q ha hb
    | true =>
      simp only [d144760, d145797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144761 q = 1) (hb : d145798 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144761, d145798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144761, d145798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144768 q = 1) (hb : d145805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144768, d145805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26790 q ha hb
    | true =>
      simp only [d144768, d145805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144769 q = 1) (hb : d145806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144769, d145806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144769, d145806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144770 q = 1) (hb : d145807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144770, d145807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144770, d145807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144771 q = 1) (hb : d145808 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144771, d145808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144771, d145808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144772 q = 1) (hb : d145809 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144772, d145809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144772, d145809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144773 q = 1) (hb : d145810 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144773, d145810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144773, d145810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26792 (p : Pattern) (ha : d52882 p = 1) (hb : d145813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5584 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5584, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5584, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15036 q ha hb
  have h3 (q : Pattern) (ha : d5540 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15036 q ha hb
    | true =>
      simp only [d5540, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d5585 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5585, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5585, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5541 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5541, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5586 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5586, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5586, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5587 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5587, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5587, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5588 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52882 q = 1) (hb : d145813 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26793 (p : Pattern) (ha : d144759 p = 1) (hb : d145819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144746 q = 1) (hb : d145781 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144746, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26785 q ha hb
    | true =>
      simp only [d144746, d145781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144747 q = 1) (hb : d145782 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144747, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144747, d145782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144748 q = 1) (hb : d145783 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144748, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144748, d145783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144749 q = 1) (hb : d145786 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144749, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26786 q ha hb
    | true =>
      simp only [d144749, d145786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144750 q = 1) (hb : d145787 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144750, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144750, d145787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144751 q = 1) (hb : d145788 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144751, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144751, d145788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144752 q = 1) (hb : d145789 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144752, d145789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144752, d145789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144749 q = 1) (hb : d145814 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144749, d145814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26792 q ha hb
    | true =>
      simp only [d144749, d145814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144750 q = 1) (hb : d145815 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144750, d145815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144750, d145815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144751 q = 1) (hb : d145816 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144751, d145816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144751, d145816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d144757 q = 1) (hb : d145817 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144757, d145817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144757, d145817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144758 q = 1) (hb : d145818 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144758, d145818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144758, d145818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144759 q = 1) (hb : d145819 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144759, d145819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144759, d145819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro26794 (p : Pattern) (ha : d144784 p = 1) (hb : d145825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144760 q = 1) (hb : d145820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144760, d145820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26793 q ha hb
    | true =>
      simp only [d144760, d145820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144761 q = 1) (hb : d145821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144761, d145821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144761, d145821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144781 q = 1) (hb : d145822 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144781, d145822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144781, d145822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144782 q = 1) (hb : d145823 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144782, d145823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144782, d145823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144783 q = 1) (hb : d145824 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144783, d145824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144783, d145824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144784 q = 1) (hb : d145825 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144784, d145825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144784, d145825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26795 (p : Pattern) (ha : d144790 p = 1) (hb : d145831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144774 q = 1) (hb : d145811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144774, d145811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26789 q ha hb
    | true =>
      simp only [d144774, d145811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26791 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144780 q = 1) (hb : d145812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144780, d145812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144780, d145812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d144785 q = 1) (hb : d145826 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144785, d145826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26794 q ha hb
    | true =>
      simp only [d144785, d145826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144786 q = 1) (hb : d145827 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144786, d145827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144786, d145827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144787 q = 1) (hb : d145828 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144787, d145828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144787, d145828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144788 q = 1) (hb : d145829 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144788, d145829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144788, d145829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144789 q = 1) (hb : d145830 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144789, d145830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144789, d145830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144790 q = 1) (hb : d145831 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144790, d145831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144790, d145831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26796 (p : Pattern) (ha : d144778 p = 1) (hb : d145836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144768 q = 1) (hb : d145805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144768, d145805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26790 q ha hb
    | true =>
      simp only [d144768, d145805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144769 q = 1) (hb : d145806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144769, d145806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144769, d145806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144775 q = 1) (hb : d145833 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144775, d145833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144775, d145833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144776 q = 1) (hb : d145834 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144776, d145834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144776, d145834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144777 q = 1) (hb : d145835 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144777, d145835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144777, d145835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144778 q = 1) (hb : d145836 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144778, d145836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144778, d145836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26797 (p : Pattern) (ha : d144797 p = 1) (hb : d145842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144792 q = 1) (hb : d145837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144792, d145837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26796 q ha hb
    | true =>
      simp only [d144792, d145837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144793 q = 1) (hb : d145838 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144793, d145838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144793, d145838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144794 q = 1) (hb : d145839 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144794, d145839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144794, d145839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144795 q = 1) (hb : d145840 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144795, d145840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144795, d145840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144796 q = 1) (hb : d145841 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144796, d145841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144796, d145841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144797 q = 1) (hb : d145842 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144797, d145842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144797, d145842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26798 (p : Pattern) (ha : d144803 p = 1) (hb : d145848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144634 q = 1) (hb : d145664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144634, d145664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144634, d145664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26758 q ha hb
  have h2 (q : Pattern) (ha : d144635 q = 1) (hb : d145665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144635, d145665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144635, d145665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d144644 q = 1) (hb : d145674 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144644, d145674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26758 q ha hb
    | true =>
      simp only [d144644, d145674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26761 q ha hb
  have h4 (q : Pattern) (ha : d144645 q = 1) (hb : d145675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144645, d145675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144645, d145675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144646 q = 1) (hb : d145676 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144646, d145676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144646, d145676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144712 q = 1) (hb : d145749 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144712, d145749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26772 q ha hb
    | true =>
      simp only [d144712, d145749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26779 q ha hb
  have h7 (q : Pattern) (ha : d144725 q = 1) (hb : d145762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144725, d145762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26780 q ha hb
    | true =>
      simp only [d144725, d145762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26781 q ha hb
  have h8 (q : Pattern) (ha : d144726 q = 1) (hb : d145763 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144726, d145763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144726, d145763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144727 q = 1) (hb : d145764 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144727, d145764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144727, d145764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144728 q = 1) (hb : d145765 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144728, d145765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144728, d145765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144732 q = 1) (hb : d145769 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144732, d145769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144732, d145769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26782 q ha hb
  have h12 (q : Pattern) (ha : d144734 q = 1) (hb : d145771 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144734, d145771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144734, d145771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26783 q ha hb
  have h13 (q : Pattern) (ha : d144735 q = 1) (hb : d145772 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144735, d145772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144735, d145772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144736 q = 1) (hb : d145773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144736, d145773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144736, d145773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d144737 q = 1) (hb : d145774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144737, d145774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d144737, d145774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d144738 q = 1) (hb : d145775 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144738, d145775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144738, d145775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d144791 q = 1) (hb : d145832 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144791, d145832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144791, d145832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26795 q ha hb
  have h18 (q : Pattern) (ha : d144798 q = 1) (hb : d145843 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144798, d145843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144798, d145843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26797 q ha hb
  have h19 (q : Pattern) (ha : d144799 q = 1) (hb : d145844 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144799, d145844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d144799, d145844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d144800 q = 1) (hb : d145845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144800, d145845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d144800, d145845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d144801 q = 1) (hb : d145846 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144801, d145846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d144801, d145846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d144802 q = 1) (hb : d145847 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144802, d145847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d144802, d145847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d144803 q = 1) (hb : d145848 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d144803, d145848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d144803, d145848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26799 (p : Pattern) (ha : d144809 p = 1) (hb : d145854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144804 q = 1) (hb : d145849 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d144804, d145849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144804, d145849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26798 q ha hb
  have h2 (q : Pattern) (ha : d144805 q = 1) (hb : d145850 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d144805, d145850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144805, d145850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144806 q = 1) (hb : d145851 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d144806, d145851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144806, d145851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144807 q = 1) (hb : d145852 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d144807, d145852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144807, d145852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144808 q = 1) (hb : d145853 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d144808, d145853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144808, d145853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144809 q = 1) (hb : d145854 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d144809, d145854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144809, d145854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26800 (p : Pattern) (ha : d53014 p = 1) (hb : d145858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1572 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1573 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15155 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53014 q = 1) (hb : d145858 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26801 (p : Pattern) (ha : d53026 p = 1) (hb : d145862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1584 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1585 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1588 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53026 q = 1) (hb : d145862 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26802 (p : Pattern) (ha : d144822 p = 1) (hb : d145869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144813 q = 1) (hb : d145859 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144813, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26800 q ha hb
    | true =>
      simp only [d144813, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144814 q = 1) (hb : d145860 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144814, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144814, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144815 q = 1) (hb : d145861 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144815, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144815, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144816 q = 1) (hb : d145863 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144816, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26801 q ha hb
    | true =>
      simp only [d144816, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144817 q = 1) (hb : d145864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144817, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144817, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144818 q = 1) (hb : d145865 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144818, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144818, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144819 q = 1) (hb : d145866 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144819, d145866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144819, d145866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144820 q = 1) (hb : d145867 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144820, d145867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144820, d145867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144821 q = 1) (hb : d145868 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144821, d145868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144821, d145868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144822 q = 1) (hb : d145869 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144822, d145869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144822, d145869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro26803 (p : Pattern) (ha : d144826 p = 1) (hb : d145873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144816 q = 1) (hb : d145863 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144816, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26801 q ha hb
    | true =>
      simp only [d144816, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144817 q = 1) (hb : d145864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144817, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144817, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144818 q = 1) (hb : d145865 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144818, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144818, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144820 q = 1) (hb : d145867 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144820, d145867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144820, d145867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144825 q = 1) (hb : d145872 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144825, d145872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144825, d145872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144826 q = 1) (hb : d145873 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144826, d145873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144826, d145873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26804 (p : Pattern) (ha : d144832 p = 1) (hb : d145879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144823 q = 1) (hb : d145870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26802 q ha hb
    | true =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144824 q = 1) (hb : d145871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144827 q = 1) (hb : d145874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26803 q ha hb
    | true =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144828 q = 1) (hb : d145875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144829 q = 1) (hb : d145876 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144829, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144829, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144830 q = 1) (hb : d145877 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144830, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144830, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144831 q = 1) (hb : d145878 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144831, d145878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144831, d145878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144832 q = 1) (hb : d145879 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144832, d145879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144832, d145879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26805 (p : Pattern) (ha : d144836 p = 1) (hb : d145883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144827 q = 1) (hb : d145874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26803 q ha hb
    | true =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144828 q = 1) (hb : d145875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144833 q = 1) (hb : d145880 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144833, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144833, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144834 q = 1) (hb : d145881 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144834, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144834, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144835 q = 1) (hb : d145882 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144835, d145882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144835, d145882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144836 q = 1) (hb : d145883 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144836, d145883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144836, d145883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26806 (p : Pattern) (ha : d144842 p = 1) (hb : d145889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144837 q = 1) (hb : d145884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144837, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26804 q ha hb
    | true =>
      simp only [d144837, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26805 q ha hb
  have h2 (q : Pattern) (ha : d144838 q = 1) (hb : d145885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144838, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144838, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144839 q = 1) (hb : d145886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144839, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144839, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144840 q = 1) (hb : d145887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144840, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144840, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144841 q = 1) (hb : d145888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144841, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144841, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144842 q = 1) (hb : d145889 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144842, d145889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144842, d145889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26807 (p : Pattern) (ha : d144845 p = 1) (hb : d145892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144823 q = 1) (hb : d145870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26802 q ha hb
    | true =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144824 q = 1) (hb : d145871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144827 q = 1) (hb : d145874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26803 q ha hb
    | true =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144828 q = 1) (hb : d145875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144829 q = 1) (hb : d145876 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144829, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144829, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144830 q = 1) (hb : d145877 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144830, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144830, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144831 q = 1) (hb : d145878 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144831, d145878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144831, d145878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144845 q = 1) (hb : d145892 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144845, d145892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144845, d145892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26808 (p : Pattern) (ha : d144846 p = 1) (hb : d145893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144827 q = 1) (hb : d145874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26803 q ha hb
    | true =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144828 q = 1) (hb : d145875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144833 q = 1) (hb : d145880 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144833, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144833, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144834 q = 1) (hb : d145881 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144834, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144834, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144835 q = 1) (hb : d145882 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144835, d145882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144835, d145882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144846 q = 1) (hb : d145893 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144846, d145893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144846, d145893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26809 (p : Pattern) (ha : d144852 p = 1) (hb : d145899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144837 q = 1) (hb : d145884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144837, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26804 q ha hb
    | true =>
      simp only [d144837, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26805 q ha hb
  have h2 (q : Pattern) (ha : d144838 q = 1) (hb : d145885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144838, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144838, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144839 q = 1) (hb : d145886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144839, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144839, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144840 q = 1) (hb : d145887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144840, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144840, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144841 q = 1) (hb : d145888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144841, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144841, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144847 q = 1) (hb : d145894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144847, d145894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26807 q ha hb
    | true =>
      simp only [d144847, d145894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26808 q ha hb
  have h7 (q : Pattern) (ha : d144848 q = 1) (hb : d145895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144848, d145895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144848, d145895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144849 q = 1) (hb : d145896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144849, d145896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144849, d145896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144850 q = 1) (hb : d145897 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144850, d145897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144850, d145897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144851 q = 1) (hb : d145898 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144851, d145898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144851, d145898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144852 q = 1) (hb : d145899 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144852, d145899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144852, d145899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26810 (p : Pattern) (ha : d144857 p = 1) (hb : d145904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144823 q = 1) (hb : d145870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26802 q ha hb
    | true =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144824 q = 1) (hb : d145871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144827 q = 1) (hb : d145874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26803 q ha hb
    | true =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144828 q = 1) (hb : d145875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144829 q = 1) (hb : d145876 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144829, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144829, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144830 q = 1) (hb : d145877 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144830, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144830, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144856 q = 1) (hb : d145903 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144856, d145903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144856, d145903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144857 q = 1) (hb : d145904 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144857, d145904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144857, d145904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26811 (p : Pattern) (ha : d144859 p = 1) (hb : d145906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144827 q = 1) (hb : d145874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26803 q ha hb
    | true =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144828 q = 1) (hb : d145875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144833 q = 1) (hb : d145880 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144833, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144833, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144834 q = 1) (hb : d145881 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144834, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144834, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144858 q = 1) (hb : d145905 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144858, d145905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144858, d145905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144859 q = 1) (hb : d145906 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144859, d145906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144859, d145906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26812 (p : Pattern) (ha : d144866 p = 1) (hb : d145913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144823 q = 1) (hb : d145870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26802 q ha hb
    | true =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144824 q = 1) (hb : d145871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144827 q = 1) (hb : d145874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26803 q ha hb
    | true =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144828 q = 1) (hb : d145875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144829 q = 1) (hb : d145876 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144829, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144829, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144864 q = 1) (hb : d145911 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144864, d145911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144864, d145911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144865 q = 1) (hb : d145912 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144865, d145912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144865, d145912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144866 q = 1) (hb : d145913 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144866, d145913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144866, d145913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26813 (p : Pattern) (ha : d144869 p = 1) (hb : d145916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144827 q = 1) (hb : d145874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26803 q ha hb
    | true =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144828 q = 1) (hb : d145875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144833 q = 1) (hb : d145880 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144833, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144833, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144867 q = 1) (hb : d145914 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144867, d145914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144867, d145914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144868 q = 1) (hb : d145915 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144868, d145915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144868, d145915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144869 q = 1) (hb : d145916 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144869, d145916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144869, d145916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26814 (p : Pattern) (ha : d52999 p = 1) (hb : d145920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1557 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1558 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15150 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52999 q = 1) (hb : d145920 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26815 (p : Pattern) (ha : d144881 p = 1) (hb : d145926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144873 q = 1) (hb : d145921 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144873, d145921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26814 q ha hb
    | true =>
      simp only [d144873, d145921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144874 q = 1) (hb : d145922 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144874, d145922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144874, d145922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144875 q = 1) (hb : d145923 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144875, d145923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144875, d145923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113614 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d144876 q = 1) (hb : d145859 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144876, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26800 q ha hb
    | true =>
      simp only [d144876, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144877 q = 1) (hb : d145860 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144877, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144877, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144878 q = 1) (hb : d145861 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144878, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144878, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144879 q = 1) (hb : d145924 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144879, d145924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144879, d145924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d144813 q = 1) (hb : d145859 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144813, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26800 q ha hb
    | true =>
      simp only [d144813, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d144814 q = 1) (hb : d145860 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144814, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144814, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d144815 q = 1) (hb : d145861 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144815, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144815, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144816 q = 1) (hb : d145863 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144816, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26801 q ha hb
    | true =>
      simp only [d144816, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d144817 q = 1) (hb : d145864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144817, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144817, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144818 q = 1) (hb : d145865 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144818, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144818, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d144819 q = 1) (hb : d145866 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144819, d145866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144819, d145866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d144880 q = 1) (hb : d145925 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144880, d145925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144880, d145925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d144881 q = 1) (hb : d145926 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144881, d145926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d144881, d145926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h19 p ha hb
theorem andIntro26816 (p : Pattern) (ha : d144887 p = 1) (hb : d145932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144882 q = 1) (hb : d145927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144882, d145927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26815 q ha hb
    | true =>
      simp only [d144882, d145927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144883 q = 1) (hb : d145928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144883, d145928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144883, d145928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144823 q = 1) (hb : d145870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26802 q ha hb
    | true =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144824 q = 1) (hb : d145871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144884 q = 1) (hb : d145929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144884, d145929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144884, d145929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144885 q = 1) (hb : d145930 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144885, d145930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144885, d145930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144886 q = 1) (hb : d145931 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144886, d145931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144886, d145931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144887 q = 1) (hb : d145932 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144887, d145932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144887, d145932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26817 (p : Pattern) (ha : d53026 p = 1) (hb : d145935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5630 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15070 q ha hb
    | true =>
      simp only [d5630, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5631 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5631, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d5632 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5632, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5632, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5633 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5633, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5633, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5634 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53026 q = 1) (hb : d145935 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d145935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26818 (p : Pattern) (ha : d144822 p = 1) (hb : d145941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144813 q = 1) (hb : d145859 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144813, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26800 q ha hb
    | true =>
      simp only [d144813, d145859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144814 q = 1) (hb : d145860 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144814, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144814, d145860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144815 q = 1) (hb : d145861 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144815, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144815, d145861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144816 q = 1) (hb : d145863 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144816, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26801 q ha hb
    | true =>
      simp only [d144816, d145863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144817 q = 1) (hb : d145864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144817, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144817, d145864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144818 q = 1) (hb : d145865 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144818, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144818, d145865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144819 q = 1) (hb : d145866 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144819, d145866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144819, d145866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144816 q = 1) (hb : d145936 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144816, d145936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26817 q ha hb
    | true =>
      simp only [d144816, d145936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144817 q = 1) (hb : d145937 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144817, d145937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144817, d145937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144818 q = 1) (hb : d145938 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144818, d145938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144818, d145938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d144820 q = 1) (hb : d145939 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144820, d145939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144820, d145939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144821 q = 1) (hb : d145940 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144821, d145940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144821, d145940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144822 q = 1) (hb : d145941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144822, d145941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144822, d145941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro26819 (p : Pattern) (ha : d144893 p = 1) (hb : d145947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144823 q = 1) (hb : d145942 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144823, d145942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26818 q ha hb
    | true =>
      simp only [d144823, d145942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144824 q = 1) (hb : d145943 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144824, d145943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144824, d145943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144890 q = 1) (hb : d145944 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144890, d145944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144890, d145944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144891 q = 1) (hb : d145945 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144891, d145945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144891, d145945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144892 q = 1) (hb : d145946 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144892, d145946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144892, d145946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144893 q = 1) (hb : d145947 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144893, d145947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144893, d145947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26820 (p : Pattern) (ha : d144899 p = 1) (hb : d145953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144860 q = 1) (hb : d145907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144860, d145907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26810 q ha hb
    | true =>
      simp only [d144860, d145907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26811 q ha hb
  have h2 (q : Pattern) (ha : d144861 q = 1) (hb : d145908 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144861, d145908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144861, d145908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144862 q = 1) (hb : d145909 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144862, d145909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144862, d145909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144863 q = 1) (hb : d145910 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144863, d145910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144863, d145910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144870 q = 1) (hb : d145917 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144870, d145917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26812 q ha hb
    | true =>
      simp only [d144870, d145917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26813 q ha hb
  have h6 (q : Pattern) (ha : d144871 q = 1) (hb : d145918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144871, d145918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144871, d145918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144872 q = 1) (hb : d145919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144872, d145919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144872, d145919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144888 q = 1) (hb : d145933 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144888, d145933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26816 q ha hb
    | true =>
      simp only [d144888, d145933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26804 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144837 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d144889 q = 1) (hb : d145934 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144889, d145934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144889, d145934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d144894 q = 1) (hb : d145948 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144894, d145948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26819 q ha hb
    | true =>
      simp only [d144894, d145948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d144895 q = 1) (hb : d145949 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144895, d145949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144895, d145949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144896 q = 1) (hb : d145950 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144896, d145950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144896, d145950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144897 q = 1) (hb : d145951 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144897, d145951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144897, d145951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144898 q = 1) (hb : d145952 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144898, d145952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144898, d145952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144899 q = 1) (hb : d145953 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144899, d145953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144899, d145953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro26821 (p : Pattern) (ha : d144900 p = 1) (hb : d145954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144823 q = 1) (hb : d145870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26802 q ha hb
    | true =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144824 q = 1) (hb : d145871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144827 q = 1) (hb : d145874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26803 q ha hb
    | true =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144828 q = 1) (hb : d145875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144829 q = 1) (hb : d145876 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144829, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144829, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144830 q = 1) (hb : d145877 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144830, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144830, d145877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144856 q = 1) (hb : d145903 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144856, d145903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144856, d145903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144900 q = 1) (hb : d145954 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144900, d145954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144900, d145954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26822 (p : Pattern) (ha : d144901 p = 1) (hb : d145955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144827 q = 1) (hb : d145874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26803 q ha hb
    | true =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144828 q = 1) (hb : d145875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144833 q = 1) (hb : d145880 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144833, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144833, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144834 q = 1) (hb : d145881 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144834, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144834, d145881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144858 q = 1) (hb : d145905 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144858, d145905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144858, d145905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144901 q = 1) (hb : d145955 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144901, d145955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144901, d145955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26823 (p : Pattern) (ha : d144906 p = 1) (hb : d145960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144823 q = 1) (hb : d145870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26802 q ha hb
    | true =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144824 q = 1) (hb : d145871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144827 q = 1) (hb : d145874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26803 q ha hb
    | true =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144828 q = 1) (hb : d145875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144829 q = 1) (hb : d145876 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144829, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144829, d145876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144864 q = 1) (hb : d145911 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144864, d145911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144864, d145911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144865 q = 1) (hb : d145912 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144865, d145912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144865, d145912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144906 q = 1) (hb : d145960 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144906, d145960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144906, d145960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26824 (p : Pattern) (ha : d144907 p = 1) (hb : d145961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144827 q = 1) (hb : d145874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26803 q ha hb
    | true =>
      simp only [d144827, d145874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144828 q = 1) (hb : d145875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144828, d145875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144833 q = 1) (hb : d145880 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144833, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144833, d145880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144867 q = 1) (hb : d145914 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144867, d145914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144867, d145914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144868 q = 1) (hb : d145915 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144868, d145915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144868, d145915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144907 q = 1) (hb : d145961 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144907, d145961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144907, d145961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26825 (p : Pattern) (ha : d144911 p = 1) (hb : d145965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144882 q = 1) (hb : d145927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144882, d145927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26815 q ha hb
    | true =>
      simp only [d144882, d145927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144883 q = 1) (hb : d145928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144883, d145928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144883, d145928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144823 q = 1) (hb : d145870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26802 q ha hb
    | true =>
      simp only [d144823, d145870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144824 q = 1) (hb : d145871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144824, d145871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144884 q = 1) (hb : d145929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144884, d145929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144884, d145929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144885 q = 1) (hb : d145930 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144885, d145930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144885, d145930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144886 q = 1) (hb : d145931 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144886, d145931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144886, d145931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144911 q = 1) (hb : d145965 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144911, d145965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144911, d145965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26826 (p : Pattern) (ha : d144914 p = 1) (hb : d145968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144823 q = 1) (hb : d145942 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144823, d145942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26818 q ha hb
    | true =>
      simp only [d144823, d145942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144824 q = 1) (hb : d145943 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144824, d145943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144824, d145943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144890 q = 1) (hb : d145944 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144890, d145944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144890, d145944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144891 q = 1) (hb : d145945 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144891, d145945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144891, d145945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144892 q = 1) (hb : d145946 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144892, d145946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144892, d145946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144914 q = 1) (hb : d145968 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144914, d145968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144914, d145968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26827 (p : Pattern) (ha : d144920 p = 1) (hb : d145974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144860 q = 1) (hb : d145907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144860, d145907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26810 q ha hb
    | true =>
      simp only [d144860, d145907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26811 q ha hb
  have h2 (q : Pattern) (ha : d144861 q = 1) (hb : d145908 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144861, d145908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144861, d145908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144862 q = 1) (hb : d145909 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144862, d145909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144862, d145909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144863 q = 1) (hb : d145910 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144863, d145910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144863, d145910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144870 q = 1) (hb : d145917 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144870, d145917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26812 q ha hb
    | true =>
      simp only [d144870, d145917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26813 q ha hb
  have h6 (q : Pattern) (ha : d144871 q = 1) (hb : d145918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144871, d145918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144871, d145918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144872 q = 1) (hb : d145919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144872, d145919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144872, d145919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144888 q = 1) (hb : d145933 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144888, d145933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26816 q ha hb
    | true =>
      simp only [d144888, d145933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26804 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144837 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d144889 q = 1) (hb : d145934 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144889, d145934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144889, d145934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d144894 q = 1) (hb : d145948 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144894, d145948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26819 q ha hb
    | true =>
      simp only [d144894, d145948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d144895 q = 1) (hb : d145949 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144895, d145949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144895, d145949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144896 q = 1) (hb : d145950 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144896, d145950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144896, d145950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144897 q = 1) (hb : d145951 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144897, d145951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144897, d145951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d144898 q = 1) (hb : d145952 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144898, d145952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144898, d145952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144902 q = 1) (hb : d145956 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144902, d145956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26821 q ha hb
    | true =>
      simp only [d144902, d145956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26822 q ha hb
  have h17 (q : Pattern) (ha : d144903 q = 1) (hb : d145957 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144903, d145957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144903, d145957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d144904 q = 1) (hb : d145958 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144904, d145958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d144904, d145958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d144905 q = 1) (hb : d145959 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144905, d145959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144905, d145959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d144908 q = 1) (hb : d145962 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144908, d145962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26823 q ha hb
    | true =>
      simp only [d144908, d145962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26824 q ha hb
  have h21 (q : Pattern) (ha : d144909 q = 1) (hb : d145963 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144909, d145963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144909, d145963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d144910 q = 1) (hb : d145964 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144910, d145964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d144910, d145964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d144912 q = 1) (hb : d145966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144912, d145966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26825 q ha hb
    | true =>
      simp only [d144912, d145966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26807 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d144847 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d144913 q = 1) (hb : d145967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144913, d145967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d144913, d145967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d144915 q = 1) (hb : d145969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144915, d145969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26826 q ha hb
    | true =>
      simp only [d144915, d145969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d144916 q = 1) (hb : d145970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144916, d145970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d144916, d145970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d144917 q = 1) (hb : d145971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144917, d145971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d144917, d145971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d144918 q = 1) (hb : d145972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144918, d145972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d144918, d145972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d144919 q = 1) (hb : d145973 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144919, d145973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d144919, d145973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d144920 q = 1) (hb : d145974 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144920, d145974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d144920, d145974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro26828 (p : Pattern) (ha : d144927 p = 1) (hb : d145981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144837 q = 1) (hb : d145884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144837, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26804 q ha hb
    | true =>
      simp only [d144837, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26805 q ha hb
  have h2 (q : Pattern) (ha : d144838 q = 1) (hb : d145885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144838, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144838, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144839 q = 1) (hb : d145886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144839, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144839, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144840 q = 1) (hb : d145887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144840, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144840, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144841 q = 1) (hb : d145888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144841, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144841, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144922 q = 1) (hb : d145976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144922, d145976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26805 q ha hb
    | true =>
      simp only [d144922, d145976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144923 q = 1) (hb : d145977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144923, d145977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144923, d145977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144924 q = 1) (hb : d145978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144924, d145978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144924, d145978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144925 q = 1) (hb : d145979 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144925, d145979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144925, d145979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144926 q = 1) (hb : d145980 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144926, d145980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144926, d145980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144927 q = 1) (hb : d145981 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144927, d145981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144927, d145981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26829 (p : Pattern) (ha : d144933 p = 1) (hb : d145987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144922 q = 1) (hb : d145976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144922, d145976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26805 q ha hb
    | true =>
      simp only [d144922, d145976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144923 q = 1) (hb : d145977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144923, d145977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144923, d145977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144924 q = 1) (hb : d145978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144924, d145978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144924, d145978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144925 q = 1) (hb : d145979 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144925, d145979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144925, d145979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144926 q = 1) (hb : d145980 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144926, d145980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144926, d145980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144928 q = 1) (hb : d145982 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144928, d145982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26808 q ha hb
    | true =>
      simp only [d144928, d145982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144929 q = 1) (hb : d145983 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144929, d145983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144929, d145983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144930 q = 1) (hb : d145984 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144930, d145984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144930, d145984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144931 q = 1) (hb : d145985 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144931, d145985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144931, d145985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144932 q = 1) (hb : d145986 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144932, d145986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144932, d145986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144933 q = 1) (hb : d145987 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144933, d145987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144933, d145987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26830 (p : Pattern) (ha : d144940 p = 1) (hb : d145994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144912 q = 1) (hb : d145966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144912, d145966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26825 q ha hb
    | true =>
      simp only [d144912, d145966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26807 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144847 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144913 q = 1) (hb : d145967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144913, d145967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144913, d145967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d144915 q = 1) (hb : d145969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144915, d145969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26826 q ha hb
    | true =>
      simp only [d144915, d145969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144916 q = 1) (hb : d145970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144916, d145970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144916, d145970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144917 q = 1) (hb : d145971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144917, d145971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144917, d145971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144938 q = 1) (hb : d145992 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144938, d145992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144938, d145992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144939 q = 1) (hb : d145993 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144939, d145993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144939, d145993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144940 q = 1) (hb : d145994 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144940, d145994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144940, d145994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26831 (p : Pattern) (ha : d144942 p = 1) (hb : d145996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144928 q = 1) (hb : d145982 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144928, d145982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26808 q ha hb
    | true =>
      simp only [d144928, d145982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144929 q = 1) (hb : d145983 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144929, d145983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144929, d145983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144930 q = 1) (hb : d145984 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144930, d145984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144930, d145984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144931 q = 1) (hb : d145985 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144931, d145985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144931, d145985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144932 q = 1) (hb : d145986 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144932, d145986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144932, d145986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144942 q = 1) (hb : d145996 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144942, d145996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144942, d145996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26832 (p : Pattern) (ha : d53186 p = 1) (hb : d146002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1857 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
  have h3 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1858 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1859 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1860 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1860, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d15386 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53186 q = 1) (hb : d146002 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26833 (p : Pattern) (ha : d53191 p = 1) (hb : d146006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1862 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
  have h3 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1863 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1864 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1865 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d15407 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53191 q = 1) (hb : d146006 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26834 (p : Pattern) (ha : d53197 p = 1) (hb : d146011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1868 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
  have h3 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1869 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1870 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1871 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1877 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53197 q = 1) (hb : d146011 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26835 (p : Pattern) (ha : d144963 p = 1) (hb : d146017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144948 q = 1) (hb : d146003 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144948, d146003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26832 q ha hb
    | true =>
      simp only [d144948, d146003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144949 q = 1) (hb : d146004 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144949, d146004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144949, d146004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144950 q = 1) (hb : d146005 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144950, d146005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144950, d146005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113715 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d144951 q = 1) (hb : d146007 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144951, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26833 q ha hb
    | true =>
      simp only [d144951, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144952 q = 1) (hb : d146008 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144952, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144952, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144953 q = 1) (hb : d146009 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144953, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144953, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144954 q = 1) (hb : d146010 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144954, d146010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144954, d146010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d144955 q = 1) (hb : d146007 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144955, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26833 q ha hb
    | true =>
      simp only [d144955, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d144956 q = 1) (hb : d146008 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144956, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144956, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d144957 q = 1) (hb : d146009 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144957, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144957, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144958 q = 1) (hb : d146012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144958, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26834 q ha hb
    | true =>
      simp only [d144958, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d144959 q = 1) (hb : d146013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144959, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144959, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144960 q = 1) (hb : d146014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144960, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144960, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d144961 q = 1) (hb : d146015 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144961, d146015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144961, d146015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d144962 q = 1) (hb : d146016 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144962, d146016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144962, d146016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d144963 q = 1) (hb : d146017 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144963, d146017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d144963, d146017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h19 p ha hb
theorem andIntro26836 (p : Pattern) (ha : d144968 p = 1) (hb : d146022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144955 q = 1) (hb : d146007 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144955, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26833 q ha hb
    | true =>
      simp only [d144955, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144956 q = 1) (hb : d146008 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144956, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144956, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144957 q = 1) (hb : d146009 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144957, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144957, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144958 q = 1) (hb : d146012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144958, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26834 q ha hb
    | true =>
      simp only [d144958, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144959 q = 1) (hb : d146013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144959, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144959, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144960 q = 1) (hb : d146014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144960, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144960, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144961 q = 1) (hb : d146015 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144961, d146015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144961, d146015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144966 q = 1) (hb : d146020 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144966, d146020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144966, d146020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144967 q = 1) (hb : d146021 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144967, d146021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144967, d146021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144968 q = 1) (hb : d146022 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144968, d146022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144968, d146022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro26837 (p : Pattern) (ha : d144974 p = 1) (hb : d146028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144964 q = 1) (hb : d146018 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144964, d146018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26835 q ha hb
    | true =>
      simp only [d144964, d146018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144965 q = 1) (hb : d146019 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144965, d146019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144965, d146019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144969 q = 1) (hb : d146023 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144969, d146023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26836 q ha hb
    | true =>
      simp only [d144969, d146023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144970 q = 1) (hb : d146024 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144970, d146024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144970, d146024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144971 q = 1) (hb : d146025 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144971, d146025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144971, d146025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144972 q = 1) (hb : d146026 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144972, d146026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144972, d146026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144973 q = 1) (hb : d146027 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144973, d146027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144973, d146027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144974 q = 1) (hb : d146028 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144974, d146028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144974, d146028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26838 (p : Pattern) (ha : d144976 p = 1) (hb : d146030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144958 q = 1) (hb : d146012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144958, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26834 q ha hb
    | true =>
      simp only [d144958, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144959 q = 1) (hb : d146013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144959, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144959, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144960 q = 1) (hb : d146014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144960, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144960, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144966 q = 1) (hb : d146020 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144966, d146020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144966, d146020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144975 q = 1) (hb : d146029 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144975, d146029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144975, d146029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144976 q = 1) (hb : d146030 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144976, d146030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144976, d146030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26839 (p : Pattern) (ha : d144982 p = 1) (hb : d146036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144969 q = 1) (hb : d146023 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144969, d146023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26836 q ha hb
    | true =>
      simp only [d144969, d146023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144970 q = 1) (hb : d146024 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144970, d146024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144970, d146024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144977 q = 1) (hb : d146031 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144977, d146031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26838 q ha hb
    | true =>
      simp only [d144977, d146031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144978 q = 1) (hb : d146032 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144978, d146032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144978, d146032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144979 q = 1) (hb : d146033 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144979, d146033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144979, d146033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144980 q = 1) (hb : d146034 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144980, d146034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144980, d146034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144981 q = 1) (hb : d146035 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144981, d146035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144981, d146035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144982 q = 1) (hb : d146036 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144982, d146036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144982, d146036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26840 (p : Pattern) (ha : d53197 p = 1) (hb : d146039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5674 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5674, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5674, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15070 q ha hb
  have h3 (q : Pattern) (ha : d5630 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15070 q ha hb
    | true =>
      simp only [d5630, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d5675 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5675, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5675, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5631 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5631, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5676 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5676, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5676, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5677 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5677, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5677, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5678 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53197 q = 1) (hb : d146039 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26841 (p : Pattern) (ha : d144968 p = 1) (hb : d146045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144955 q = 1) (hb : d146007 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144955, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26833 q ha hb
    | true =>
      simp only [d144955, d146007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d144956 q = 1) (hb : d146008 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144956, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144956, d146008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144957 q = 1) (hb : d146009 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144957, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144957, d146009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144958 q = 1) (hb : d146012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144958, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26834 q ha hb
    | true =>
      simp only [d144958, d146012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144959 q = 1) (hb : d146013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144959, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144959, d146013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144960 q = 1) (hb : d146014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144960, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144960, d146014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144961 q = 1) (hb : d146015 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144961, d146015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144961, d146015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144958 q = 1) (hb : d146040 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144958, d146040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26840 q ha hb
    | true =>
      simp only [d144958, d146040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144959 q = 1) (hb : d146041 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144959, d146041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144959, d146041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144960 q = 1) (hb : d146042 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144960, d146042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144960, d146042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d144966 q = 1) (hb : d146043 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144966, d146043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144966, d146043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144967 q = 1) (hb : d146044 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144967, d146044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144967, d146044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144968 q = 1) (hb : d146045 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144968, d146045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144968, d146045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro26842 (p : Pattern) (ha : d144993 p = 1) (hb : d146051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144969 q = 1) (hb : d146046 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144969, d146046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26841 q ha hb
    | true =>
      simp only [d144969, d146046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144970 q = 1) (hb : d146047 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144970, d146047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144970, d146047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144990 q = 1) (hb : d146048 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144990, d146048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144990, d146048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144991 q = 1) (hb : d146049 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144991, d146049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144991, d146049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144992 q = 1) (hb : d146050 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144992, d146050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144992, d146050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144993 q = 1) (hb : d146051 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144993, d146051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144993, d146051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26843 (p : Pattern) (ha : d144999 p = 1) (hb : d146057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144983 q = 1) (hb : d146037 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144983, d146037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26837 q ha hb
    | true =>
      simp only [d144983, d146037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26839 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144989 q = 1) (hb : d146038 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144989, d146038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144989, d146038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d144994 q = 1) (hb : d146052 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144994, d146052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26842 q ha hb
    | true =>
      simp only [d144994, d146052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144995 q = 1) (hb : d146053 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144995, d146053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144995, d146053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144996 q = 1) (hb : d146054 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144996, d146054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144996, d146054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144997 q = 1) (hb : d146055 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144997, d146055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144997, d146055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144998 q = 1) (hb : d146056 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144998, d146056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144998, d146056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144999 q = 1) (hb : d146057 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144999, d146057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144999, d146057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26844 (p : Pattern) (ha : d144987 p = 1) (hb : d146062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144977 q = 1) (hb : d146031 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144977, d146031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26838 q ha hb
    | true =>
      simp only [d144977, d146031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144978 q = 1) (hb : d146032 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144978, d146032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144978, d146032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144984 q = 1) (hb : d146059 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144984, d146059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144984, d146059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144985 q = 1) (hb : d146060 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144985, d146060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144985, d146060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144986 q = 1) (hb : d146061 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144986, d146061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144986, d146061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144987 q = 1) (hb : d146062 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144987, d146062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144987, d146062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26845 (p : Pattern) (ha : d145006 p = 1) (hb : d146068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145001 q = 1) (hb : d146063 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145001, d146063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26844 q ha hb
    | true =>
      simp only [d145001, d146063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145002 q = 1) (hb : d146064 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145002, d146064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145002, d146064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145003 q = 1) (hb : d146065 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145003, d146065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145003, d146065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145004 q = 1) (hb : d146066 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145004, d146066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145004, d146066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145005 q = 1) (hb : d146067 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145005, d146067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145005, d146067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145006 q = 1) (hb : d146068 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145006, d146068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145006, d146068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26846 (p : Pattern) (ha : d145012 p = 1) (hb : d146074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144843 q = 1) (hb : d145890 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144843, d145890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144843, d145890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26806 q ha hb
  have h2 (q : Pattern) (ha : d144844 q = 1) (hb : d145891 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144844, d145891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144844, d145891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d144853 q = 1) (hb : d145900 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144853, d145900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26806 q ha hb
    | true =>
      simp only [d144853, d145900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26809 q ha hb
  have h4 (q : Pattern) (ha : d144854 q = 1) (hb : d145901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144854, d145901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144854, d145901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144855 q = 1) (hb : d145902 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144855, d145902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144855, d145902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144921 q = 1) (hb : d145975 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144921, d145975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26820 q ha hb
    | true =>
      simp only [d144921, d145975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26827 q ha hb
  have h7 (q : Pattern) (ha : d144934 q = 1) (hb : d145988 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144934, d145988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26828 q ha hb
    | true =>
      simp only [d144934, d145988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26829 q ha hb
  have h8 (q : Pattern) (ha : d144935 q = 1) (hb : d145989 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144935, d145989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144935, d145989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144936 q = 1) (hb : d145990 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144936, d145990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144936, d145990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d144937 q = 1) (hb : d145991 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144937, d145991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144937, d145991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144941 q = 1) (hb : d145995 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144941, d145995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144941, d145995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26830 q ha hb
  have h12 (q : Pattern) (ha : d144943 q = 1) (hb : d145997 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144943, d145997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144943, d145997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26831 q ha hb
  have h13 (q : Pattern) (ha : d144944 q = 1) (hb : d145998 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144944, d145998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144944, d145998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d144945 q = 1) (hb : d145999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144945, d145999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144945, d145999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d144946 q = 1) (hb : d146000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144946, d146000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d144946, d146000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d144947 q = 1) (hb : d146001 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144947, d146001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144947, d146001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d145000 q = 1) (hb : d146058 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145000, d146058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145000, d146058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26843 q ha hb
  have h18 (q : Pattern) (ha : d145007 q = 1) (hb : d146069 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145007, d146069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145007, d146069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26845 q ha hb
  have h19 (q : Pattern) (ha : d145008 q = 1) (hb : d146070 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145008, d146070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d145008, d146070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d145009 q = 1) (hb : d146071 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d145009, d146071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d145009, d146071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d145010 q = 1) (hb : d146072 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d145010, d146072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d145010, d146072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d145011 q = 1) (hb : d146073 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d145011, d146073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d145011, d146073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d145012 q = 1) (hb : d146074 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d145012, d146074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d145012, d146074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26847 (p : Pattern) (ha : d145018 p = 1) (hb : d146080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145013 q = 1) (hb : d146075 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d145013, d146075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145013, d146075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26846 q ha hb
  have h2 (q : Pattern) (ha : d145014 q = 1) (hb : d146076 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d145014, d146076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145014, d146076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145015 q = 1) (hb : d146077 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d145015, d146077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145015, d146077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145016 q = 1) (hb : d146078 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d145016, d146078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145016, d146078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145017 q = 1) (hb : d146079 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d145017, d146079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145017, d146079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145018 q = 1) (hb : d146080 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d145018, d146080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145018, d146080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26848 (p : Pattern) (ha : d53335 p = 1) (hb : d146085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2055 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2056 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15547 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53335 q = 1) (hb : d146085 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26849 (p : Pattern) (ha : d53347 p = 1) (hb : d146089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2067 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2068 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2071 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53347 q = 1) (hb : d146089 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26850 (p : Pattern) (ha : d145032 p = 1) (hb : d146096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145023 q = 1) (hb : d146086 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145023, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26848 q ha hb
    | true =>
      simp only [d145023, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d145024 q = 1) (hb : d146087 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145024, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145024, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145025 q = 1) (hb : d146088 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145025, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145025, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145026 q = 1) (hb : d146090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145026, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26849 q ha hb
    | true =>
      simp only [d145026, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145027 q = 1) (hb : d146091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145027, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145027, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145028 q = 1) (hb : d146092 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145028, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145028, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145029 q = 1) (hb : d146093 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145029, d146093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145029, d146093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145030 q = 1) (hb : d146094 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145030, d146094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145030, d146094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d145031 q = 1) (hb : d146095 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d145031, d146095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d145031, d146095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145032 q = 1) (hb : d146096 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d145032, d146096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d145032, d146096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro26851 (p : Pattern) (ha : d145036 p = 1) (hb : d146100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145026 q = 1) (hb : d146090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145026, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26849 q ha hb
    | true =>
      simp only [d145026, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145027 q = 1) (hb : d146091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145027, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145027, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145028 q = 1) (hb : d146092 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145028, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145028, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145030 q = 1) (hb : d146094 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145030, d146094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145030, d146094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145035 q = 1) (hb : d146099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d145035, d146099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145035, d146099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145036 q = 1) (hb : d146100 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d145036, d146100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145036, d146100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26852 (p : Pattern) (ha : d145042 p = 1) (hb : d146106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145033 q = 1) (hb : d146097 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26850 q ha hb
    | true =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145034 q = 1) (hb : d146098 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145037 q = 1) (hb : d146101 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26851 q ha hb
    | true =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145038 q = 1) (hb : d146102 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145039 q = 1) (hb : d146103 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145039, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145039, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145040 q = 1) (hb : d146104 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145040, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145040, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d145041 q = 1) (hb : d146105 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145041, d146105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145041, d146105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d145042 q = 1) (hb : d146106 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145042, d146106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145042, d146106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26853 (p : Pattern) (ha : d145046 p = 1) (hb : d146110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145037 q = 1) (hb : d146101 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26851 q ha hb
    | true =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145038 q = 1) (hb : d146102 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145043 q = 1) (hb : d146107 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145043, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145043, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145044 q = 1) (hb : d146108 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145044, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145044, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145045 q = 1) (hb : d146109 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145045, d146109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145045, d146109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145046 q = 1) (hb : d146110 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145046, d146110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145046, d146110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26854 (p : Pattern) (ha : d145052 p = 1) (hb : d146116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145047 q = 1) (hb : d146111 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145047, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26852 q ha hb
    | true =>
      simp only [d145047, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26853 q ha hb
  have h2 (q : Pattern) (ha : d145048 q = 1) (hb : d146112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145048, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145048, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145049 q = 1) (hb : d146113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145049, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145049, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145050 q = 1) (hb : d146114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145050, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145050, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145051 q = 1) (hb : d146115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145051, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145051, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145052 q = 1) (hb : d146116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145052, d146116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145052, d146116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26855 (p : Pattern) (ha : d145055 p = 1) (hb : d146119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145033 q = 1) (hb : d146097 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26850 q ha hb
    | true =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145034 q = 1) (hb : d146098 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145037 q = 1) (hb : d146101 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26851 q ha hb
    | true =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145038 q = 1) (hb : d146102 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145039 q = 1) (hb : d146103 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145039, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145039, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145040 q = 1) (hb : d146104 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145040, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145040, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d145041 q = 1) (hb : d146105 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145041, d146105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145041, d146105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d145055 q = 1) (hb : d146119 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145055, d146119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145055, d146119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26856 (p : Pattern) (ha : d145056 p = 1) (hb : d146120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145037 q = 1) (hb : d146101 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26851 q ha hb
    | true =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145038 q = 1) (hb : d146102 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145043 q = 1) (hb : d146107 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145043, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145043, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145044 q = 1) (hb : d146108 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145044, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145044, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145045 q = 1) (hb : d146109 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145045, d146109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145045, d146109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145056 q = 1) (hb : d146120 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145056, d146120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145056, d146120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26857 (p : Pattern) (ha : d145062 p = 1) (hb : d146126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145047 q = 1) (hb : d146111 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145047, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26852 q ha hb
    | true =>
      simp only [d145047, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26853 q ha hb
  have h2 (q : Pattern) (ha : d145048 q = 1) (hb : d146112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145048, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145048, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145049 q = 1) (hb : d146113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145049, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145049, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145050 q = 1) (hb : d146114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145050, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145050, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145051 q = 1) (hb : d146115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145051, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145051, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145057 q = 1) (hb : d146121 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145057, d146121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26855 q ha hb
    | true =>
      simp only [d145057, d146121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26856 q ha hb
  have h7 (q : Pattern) (ha : d145058 q = 1) (hb : d146122 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145058, d146122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145058, d146122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145059 q = 1) (hb : d146123 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145059, d146123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145059, d146123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d145060 q = 1) (hb : d146124 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145060, d146124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145060, d146124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d145061 q = 1) (hb : d146125 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145061, d146125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145061, d146125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145062 q = 1) (hb : d146126 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145062, d146126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145062, d146126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26858 (p : Pattern) (ha : d145067 p = 1) (hb : d146131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145033 q = 1) (hb : d146097 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26850 q ha hb
    | true =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145034 q = 1) (hb : d146098 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145037 q = 1) (hb : d146101 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26851 q ha hb
    | true =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145038 q = 1) (hb : d146102 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145039 q = 1) (hb : d146103 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145039, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145039, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145040 q = 1) (hb : d146104 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145040, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145040, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d145066 q = 1) (hb : d146130 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145066, d146130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145066, d146130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145067 q = 1) (hb : d146131 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145067, d146131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145067, d146131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26859 (p : Pattern) (ha : d145069 p = 1) (hb : d146133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145037 q = 1) (hb : d146101 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26851 q ha hb
    | true =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145038 q = 1) (hb : d146102 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145043 q = 1) (hb : d146107 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145043, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145043, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145044 q = 1) (hb : d146108 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145044, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145044, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145068 q = 1) (hb : d146132 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145068, d146132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145068, d146132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145069 q = 1) (hb : d146133 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145069, d146133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145069, d146133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26860 (p : Pattern) (ha : d145076 p = 1) (hb : d146140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145033 q = 1) (hb : d146097 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26850 q ha hb
    | true =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145034 q = 1) (hb : d146098 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145037 q = 1) (hb : d146101 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26851 q ha hb
    | true =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145038 q = 1) (hb : d146102 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145039 q = 1) (hb : d146103 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145039, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145039, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145074 q = 1) (hb : d146138 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145074, d146138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145074, d146138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145075 q = 1) (hb : d146139 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145075, d146139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145075, d146139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d145076 q = 1) (hb : d146140 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145076, d146140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145076, d146140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26861 (p : Pattern) (ha : d145079 p = 1) (hb : d146143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145037 q = 1) (hb : d146101 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26851 q ha hb
    | true =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145038 q = 1) (hb : d146102 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145043 q = 1) (hb : d146107 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145043, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145043, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145077 q = 1) (hb : d146141 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145077, d146141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145077, d146141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145078 q = 1) (hb : d146142 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145078, d146142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145078, d146142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145079 q = 1) (hb : d146143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145079, d146143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145079, d146143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26862 (p : Pattern) (ha : d53317 p = 1) (hb : d146147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2036 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2037 q = 1) (hb : d53316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2038 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15544 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53317 q = 1) (hb : d146147 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26863 (p : Pattern) (ha : d145091 p = 1) (hb : d146153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145083 q = 1) (hb : d146148 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145083, d146148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26862 q ha hb
    | true =>
      simp only [d145083, d146148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d145084 q = 1) (hb : d146149 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145084, d146149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145084, d146149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145085 q = 1) (hb : d146150 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145085, d146150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145085, d146150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113871 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d145086 q = 1) (hb : d146086 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145086, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26848 q ha hb
    | true =>
      simp only [d145086, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d145087 q = 1) (hb : d146087 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145087, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145087, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145088 q = 1) (hb : d146088 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145088, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145088, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145089 q = 1) (hb : d146151 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145089, d146151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145089, d146151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d145023 q = 1) (hb : d146086 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145023, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26848 q ha hb
    | true =>
      simp only [d145023, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d145024 q = 1) (hb : d146087 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145024, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145024, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d145025 q = 1) (hb : d146088 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145025, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145025, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d145026 q = 1) (hb : d146090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145026, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26849 q ha hb
    | true =>
      simp only [d145026, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d145027 q = 1) (hb : d146091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145027, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145027, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d145028 q = 1) (hb : d146092 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145028, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145028, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d145029 q = 1) (hb : d146093 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145029, d146093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d145029, d146093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d145090 q = 1) (hb : d146152 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d145090, d146152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d145090, d146152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d145091 q = 1) (hb : d146153 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d145091, d146153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d145091, d146153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h19 p ha hb
theorem andIntro26864 (p : Pattern) (ha : d145097 p = 1) (hb : d146159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145092 q = 1) (hb : d146154 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145092, d146154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26863 q ha hb
    | true =>
      simp only [d145092, d146154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145093 q = 1) (hb : d146155 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145093, d146155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145093, d146155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145033 q = 1) (hb : d146097 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26850 q ha hb
    | true =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145034 q = 1) (hb : d146098 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145094 q = 1) (hb : d146156 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145094, d146156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145094, d146156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145095 q = 1) (hb : d146157 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145095, d146157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145095, d146157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d145096 q = 1) (hb : d146158 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145096, d146158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145096, d146158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d145097 q = 1) (hb : d146159 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145097, d146159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145097, d146159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26865 (p : Pattern) (ha : d53347 p = 1) (hb : d146162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5721 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5721, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15104 q ha hb
    | true =>
      simp only [d5721, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5722 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5722, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5722, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d5723 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5723, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5723, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5724 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5724, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5724, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5725 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53347 q = 1) (hb : d146162 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro26866 (p : Pattern) (ha : d145032 p = 1) (hb : d146168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145023 q = 1) (hb : d146086 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145023, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26848 q ha hb
    | true =>
      simp only [d145023, d146086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d145024 q = 1) (hb : d146087 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145024, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145024, d146087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145025 q = 1) (hb : d146088 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145025, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145025, d146088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145026 q = 1) (hb : d146090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145026, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26849 q ha hb
    | true =>
      simp only [d145026, d146090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145027 q = 1) (hb : d146091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145027, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145027, d146091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145028 q = 1) (hb : d146092 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145028, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145028, d146092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145029 q = 1) (hb : d146093 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145029, d146093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145029, d146093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145026 q = 1) (hb : d146163 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145026, d146163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26865 q ha hb
    | true =>
      simp only [d145026, d146163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d145027 q = 1) (hb : d146164 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145027, d146164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145027, d146164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145028 q = 1) (hb : d146165 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145028, d146165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145028, d146165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d145030 q = 1) (hb : d146166 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145030, d146166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d145030, d146166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d145031 q = 1) (hb : d146167 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d145031, d146167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d145031, d146167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d145032 q = 1) (hb : d146168 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d145032, d146168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d145032, d146168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro26867 (p : Pattern) (ha : d145103 p = 1) (hb : d146174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145033 q = 1) (hb : d146169 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145033, d146169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26866 q ha hb
    | true =>
      simp only [d145033, d146169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145034 q = 1) (hb : d146170 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145034, d146170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145034, d146170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145100 q = 1) (hb : d146171 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145100, d146171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145100, d146171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145101 q = 1) (hb : d146172 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145101, d146172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145101, d146172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145102 q = 1) (hb : d146173 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145102, d146173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145102, d146173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145103 q = 1) (hb : d146174 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145103, d146174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145103, d146174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26868 (p : Pattern) (ha : d145109 p = 1) (hb : d146180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145070 q = 1) (hb : d146134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145070, d146134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26858 q ha hb
    | true =>
      simp only [d145070, d146134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26859 q ha hb
  have h2 (q : Pattern) (ha : d145071 q = 1) (hb : d146135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145071, d146135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145071, d146135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145072 q = 1) (hb : d146136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145072, d146136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145072, d146136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145073 q = 1) (hb : d146137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145073, d146137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145073, d146137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145080 q = 1) (hb : d146144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145080, d146144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26860 q ha hb
    | true =>
      simp only [d145080, d146144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26861 q ha hb
  have h6 (q : Pattern) (ha : d145081 q = 1) (hb : d146145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145081, d146145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145081, d146145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145082 q = 1) (hb : d146146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145082, d146146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145082, d146146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d145098 q = 1) (hb : d146160 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145098, d146160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26864 q ha hb
    | true =>
      simp only [d145098, d146160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26852 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d145047 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d145099 q = 1) (hb : d146161 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145099, d146161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d145099, d146161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d145104 q = 1) (hb : d146175 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145104, d146175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26867 q ha hb
    | true =>
      simp only [d145104, d146175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d145105 q = 1) (hb : d146176 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145105, d146176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d145105, d146176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d145106 q = 1) (hb : d146177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145106, d146177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d145106, d146177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d145107 q = 1) (hb : d146178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145107, d146178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145107, d146178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d145108 q = 1) (hb : d146179 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145108, d146179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145108, d146179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d145109 q = 1) (hb : d146180 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145109, d146180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145109, d146180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro26869 (p : Pattern) (ha : d145110 p = 1) (hb : d146181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145033 q = 1) (hb : d146097 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26850 q ha hb
    | true =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145034 q = 1) (hb : d146098 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145037 q = 1) (hb : d146101 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26851 q ha hb
    | true =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145038 q = 1) (hb : d146102 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145039 q = 1) (hb : d146103 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145039, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145039, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145040 q = 1) (hb : d146104 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145040, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145040, d146104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d145066 q = 1) (hb : d146130 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145066, d146130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145066, d146130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145110 q = 1) (hb : d146181 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145110, d146181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145110, d146181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26870 (p : Pattern) (ha : d145111 p = 1) (hb : d146182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145037 q = 1) (hb : d146101 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26851 q ha hb
    | true =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145038 q = 1) (hb : d146102 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145043 q = 1) (hb : d146107 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145043, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145043, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145044 q = 1) (hb : d146108 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145044, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145044, d146108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145068 q = 1) (hb : d146132 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145068, d146132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145068, d146132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145111 q = 1) (hb : d146182 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145111, d146182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145111, d146182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26871 (p : Pattern) (ha : d145116 p = 1) (hb : d146187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145033 q = 1) (hb : d146097 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26850 q ha hb
    | true =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145034 q = 1) (hb : d146098 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145037 q = 1) (hb : d146101 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26851 q ha hb
    | true =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145038 q = 1) (hb : d146102 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145039 q = 1) (hb : d146103 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145039, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145039, d146103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145074 q = 1) (hb : d146138 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145074, d146138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145074, d146138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145075 q = 1) (hb : d146139 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145075, d146139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145075, d146139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d145116 q = 1) (hb : d146187 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145116, d146187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145116, d146187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26872 (p : Pattern) (ha : d145117 p = 1) (hb : d146188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145037 q = 1) (hb : d146101 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26851 q ha hb
    | true =>
      simp only [d145037, d146101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145038 q = 1) (hb : d146102 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145038, d146102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145043 q = 1) (hb : d146107 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145043, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145043, d146107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145077 q = 1) (hb : d146141 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145077, d146141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145077, d146141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145078 q = 1) (hb : d146142 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145078, d146142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145078, d146142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145117 q = 1) (hb : d146188 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145117, d146188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145117, d146188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26873 (p : Pattern) (ha : d145121 p = 1) (hb : d146192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145092 q = 1) (hb : d146154 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145092, d146154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26863 q ha hb
    | true =>
      simp only [d145092, d146154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145093 q = 1) (hb : d146155 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145093, d146155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145093, d146155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145033 q = 1) (hb : d146097 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26850 q ha hb
    | true =>
      simp only [d145033, d146097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145034 q = 1) (hb : d146098 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145034, d146098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145094 q = 1) (hb : d146156 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145094, d146156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145094, d146156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145095 q = 1) (hb : d146157 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145095, d146157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145095, d146157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d145096 q = 1) (hb : d146158 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145096, d146158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145096, d146158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d145121 q = 1) (hb : d146192 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145121, d146192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145121, d146192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26874 (p : Pattern) (ha : d145124 p = 1) (hb : d146195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145033 q = 1) (hb : d146169 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145033, d146169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26866 q ha hb
    | true =>
      simp only [d145033, d146169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145034 q = 1) (hb : d146170 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145034, d146170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145034, d146170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145100 q = 1) (hb : d146171 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145100, d146171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145100, d146171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145101 q = 1) (hb : d146172 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145101, d146172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145101, d146172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145102 q = 1) (hb : d146173 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145102, d146173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145102, d146173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145124 q = 1) (hb : d146195 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145124, d146195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145124, d146195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26875 (p : Pattern) (ha : d145130 p = 1) (hb : d146201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145070 q = 1) (hb : d146134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145070, d146134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26858 q ha hb
    | true =>
      simp only [d145070, d146134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26859 q ha hb
  have h2 (q : Pattern) (ha : d145071 q = 1) (hb : d146135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145071, d146135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145071, d146135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145072 q = 1) (hb : d146136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145072, d146136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145072, d146136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145073 q = 1) (hb : d146137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145073, d146137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145073, d146137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145080 q = 1) (hb : d146144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145080, d146144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26860 q ha hb
    | true =>
      simp only [d145080, d146144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26861 q ha hb
  have h6 (q : Pattern) (ha : d145081 q = 1) (hb : d146145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145081, d146145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145081, d146145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145082 q = 1) (hb : d146146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145082, d146146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145082, d146146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d145098 q = 1) (hb : d146160 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145098, d146160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26864 q ha hb
    | true =>
      simp only [d145098, d146160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26852 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d145047 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d145099 q = 1) (hb : d146161 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145099, d146161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d145099, d146161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d145104 q = 1) (hb : d146175 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145104, d146175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26867 q ha hb
    | true =>
      simp only [d145104, d146175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d145105 q = 1) (hb : d146176 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145105, d146176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d145105, d146176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d145106 q = 1) (hb : d146177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145106, d146177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d145106, d146177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d145107 q = 1) (hb : d146178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145107, d146178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145107, d146178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d145108 q = 1) (hb : d146179 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145108, d146179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145108, d146179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d145112 q = 1) (hb : d146183 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145112, d146183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26869 q ha hb
    | true =>
      simp only [d145112, d146183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26870 q ha hb
  have h17 (q : Pattern) (ha : d145113 q = 1) (hb : d146184 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145113, d146184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145113, d146184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d145114 q = 1) (hb : d146185 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145114, d146185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d145114, d146185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d145115 q = 1) (hb : d146186 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145115, d146186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145115, d146186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d145118 q = 1) (hb : d146189 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145118, d146189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26871 q ha hb
    | true =>
      simp only [d145118, d146189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26872 q ha hb
  have h21 (q : Pattern) (ha : d145119 q = 1) (hb : d146190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145119, d146190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145119, d146190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d145120 q = 1) (hb : d146191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145120, d146191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d145120, d146191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d145122 q = 1) (hb : d146193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145122, d146193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26873 q ha hb
    | true =>
      simp only [d145122, d146193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26855 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d145057 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d145123 q = 1) (hb : d146194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145123, d146194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d145123, d146194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d145125 q = 1) (hb : d146196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145125, d146196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26874 q ha hb
    | true =>
      simp only [d145125, d146196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d145126 q = 1) (hb : d146197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145126, d146197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d145126, d146197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d145127 q = 1) (hb : d146198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145127, d146198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d145127, d146198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d145128 q = 1) (hb : d146199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145128, d146199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d145128, d146199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d145129 q = 1) (hb : d146200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145129, d146200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d145129, d146200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d145130 q = 1) (hb : d146201 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145130, d146201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d145130, d146201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro26876 (p : Pattern) (ha : d145137 p = 1) (hb : d146208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145047 q = 1) (hb : d146111 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145047, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26852 q ha hb
    | true =>
      simp only [d145047, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26853 q ha hb
  have h2 (q : Pattern) (ha : d145048 q = 1) (hb : d146112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145048, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145048, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145049 q = 1) (hb : d146113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145049, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145049, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145050 q = 1) (hb : d146114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145050, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145050, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145051 q = 1) (hb : d146115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145051, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145051, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145132 q = 1) (hb : d146203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145132, d146203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26853 q ha hb
    | true =>
      simp only [d145132, d146203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d145133 q = 1) (hb : d146204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145133, d146204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145133, d146204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145134 q = 1) (hb : d146205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145134, d146205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145134, d146205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d145135 q = 1) (hb : d146206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145135, d146206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145135, d146206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d145136 q = 1) (hb : d146207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145136, d146207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145136, d146207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145137 q = 1) (hb : d146208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145137, d146208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145137, d146208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26877 (p : Pattern) (ha : d145143 p = 1) (hb : d146214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145132 q = 1) (hb : d146203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145132, d146203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26853 q ha hb
    | true =>
      simp only [d145132, d146203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145133 q = 1) (hb : d146204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145133, d146204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145133, d146204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145134 q = 1) (hb : d146205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145134, d146205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145134, d146205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145135 q = 1) (hb : d146206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145135, d146206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145135, d146206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145136 q = 1) (hb : d146207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145136, d146207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145136, d146207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145138 q = 1) (hb : d146209 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145138, d146209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26856 q ha hb
    | true =>
      simp only [d145138, d146209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d145139 q = 1) (hb : d146210 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145139, d146210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145139, d146210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145140 q = 1) (hb : d146211 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145140, d146211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145140, d146211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d145141 q = 1) (hb : d146212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145141, d146212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145141, d146212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d145142 q = 1) (hb : d146213 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145142, d146213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145142, d146213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145143 q = 1) (hb : d146214 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145143, d146214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145143, d146214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26878 (p : Pattern) (ha : d145150 p = 1) (hb : d146221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145122 q = 1) (hb : d146193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145122, d146193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26873 q ha hb
    | true =>
      simp only [d145122, d146193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26855 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d145057 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145123 q = 1) (hb : d146194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145123, d146194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145123, d146194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d145125 q = 1) (hb : d146196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145125, d146196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26874 q ha hb
    | true =>
      simp only [d145125, d146196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145126 q = 1) (hb : d146197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145126, d146197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145126, d146197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145127 q = 1) (hb : d146198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145127, d146198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145127, d146198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145148 q = 1) (hb : d146219 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145148, d146219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145148, d146219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145149 q = 1) (hb : d146220 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145149, d146220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145149, d146220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145150 q = 1) (hb : d146221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145150, d146221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145150, d146221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26879 (p : Pattern) (ha : d145152 p = 1) (hb : d146223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145138 q = 1) (hb : d146209 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145138, d146209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26856 q ha hb
    | true =>
      simp only [d145138, d146209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145139 q = 1) (hb : d146210 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145139, d146210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145139, d146210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145140 q = 1) (hb : d146211 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145140, d146211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145140, d146211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145141 q = 1) (hb : d146212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145141, d146212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145141, d146212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145142 q = 1) (hb : d146213 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145142, d146213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145142, d146213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145152 q = 1) (hb : d146223 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145152, d146223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145152, d146223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26880 (p : Pattern) (ha : d53503 p = 1) (hb : d146229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2335 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
  have h3 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2336 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2036 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2337 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2338 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2338, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d15769 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53503 q = 1) (hb : d146229 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26881 (p : Pattern) (ha : d53508 p = 1) (hb : d146233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2340 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
  have h3 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2341 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2342 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2343 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d15785 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53508 q = 1) (hb : d146233 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26882 (p : Pattern) (ha : d53514 p = 1) (hb : d146238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2346 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
  have h3 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2347 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2348 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2349 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2355 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53514 q = 1) (hb : d146238 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26883 (p : Pattern) (ha : d145173 p = 1) (hb : d146244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145158 q = 1) (hb : d146230 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145158, d146230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26880 q ha hb
    | true =>
      simp only [d145158, d146230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d145159 q = 1) (hb : d146231 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145159, d146231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145159, d146231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145160 q = 1) (hb : d146232 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145160, d146232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145160, d146232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113972 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d145161 q = 1) (hb : d146234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145161, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26881 q ha hb
    | true =>
      simp only [d145161, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d145162 q = 1) (hb : d146235 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145162, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145162, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145163 q = 1) (hb : d146236 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145163, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145163, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145164 q = 1) (hb : d146237 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145164, d146237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145164, d146237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d145165 q = 1) (hb : d146234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145165, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26881 q ha hb
    | true =>
      simp only [d145165, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d145166 q = 1) (hb : d146235 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145166, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145166, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d145167 q = 1) (hb : d146236 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145167, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145167, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d145168 q = 1) (hb : d146239 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145168, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26882 q ha hb
    | true =>
      simp only [d145168, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d145169 q = 1) (hb : d146240 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145169, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145169, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d145170 q = 1) (hb : d146241 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145170, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145170, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d145171 q = 1) (hb : d146242 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145171, d146242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d145171, d146242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d145172 q = 1) (hb : d146243 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d145172, d146243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d145172, d146243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d145173 q = 1) (hb : d146244 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d145173, d146244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d145173, d146244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h19 p ha hb
theorem andIntro26884 (p : Pattern) (ha : d145178 p = 1) (hb : d146249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145165 q = 1) (hb : d146234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145165, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26881 q ha hb
    | true =>
      simp only [d145165, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d145166 q = 1) (hb : d146235 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145166, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145166, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145167 q = 1) (hb : d146236 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145167, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145167, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145168 q = 1) (hb : d146239 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145168, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26882 q ha hb
    | true =>
      simp only [d145168, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145169 q = 1) (hb : d146240 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145169, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145169, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145170 q = 1) (hb : d146241 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145170, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145170, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145171 q = 1) (hb : d146242 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145171, d146242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145171, d146242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145176 q = 1) (hb : d146247 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145176, d146247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145176, d146247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d145177 q = 1) (hb : d146248 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d145177, d146248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d145177, d146248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145178 q = 1) (hb : d146249 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d145178, d146249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d145178, d146249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro26885 (p : Pattern) (ha : d145184 p = 1) (hb : d146255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145174 q = 1) (hb : d146245 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145174, d146245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26883 q ha hb
    | true =>
      simp only [d145174, d146245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145175 q = 1) (hb : d146246 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145175, d146246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145175, d146246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145179 q = 1) (hb : d146250 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145179, d146250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26884 q ha hb
    | true =>
      simp only [d145179, d146250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145180 q = 1) (hb : d146251 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145180, d146251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145180, d146251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145181 q = 1) (hb : d146252 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145181, d146252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145181, d146252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145182 q = 1) (hb : d146253 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145182, d146253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145182, d146253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d145183 q = 1) (hb : d146254 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145183, d146254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145183, d146254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d145184 q = 1) (hb : d146255 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145184, d146255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145184, d146255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26886 (p : Pattern) (ha : d145186 p = 1) (hb : d146257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145168 q = 1) (hb : d146239 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145168, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26882 q ha hb
    | true =>
      simp only [d145168, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145169 q = 1) (hb : d146240 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145169, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145169, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145170 q = 1) (hb : d146241 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145170, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145170, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145176 q = 1) (hb : d146247 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145176, d146247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145176, d146247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145185 q = 1) (hb : d146256 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d145185, d146256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145185, d146256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145186 q = 1) (hb : d146257 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d145186, d146257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145186, d146257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26887 (p : Pattern) (ha : d145192 p = 1) (hb : d146263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145179 q = 1) (hb : d146250 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145179, d146250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26884 q ha hb
    | true =>
      simp only [d145179, d146250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145180 q = 1) (hb : d146251 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145180, d146251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145180, d146251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145187 q = 1) (hb : d146258 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145187, d146258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26886 q ha hb
    | true =>
      simp only [d145187, d146258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145188 q = 1) (hb : d146259 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145188, d146259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145188, d146259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145189 q = 1) (hb : d146260 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145189, d146260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145189, d146260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145190 q = 1) (hb : d146261 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145190, d146261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145190, d146261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d145191 q = 1) (hb : d146262 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145191, d146262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145191, d146262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d145192 q = 1) (hb : d146263 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145192, d146263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145192, d146263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26888 (p : Pattern) (ha : d53514 p = 1) (hb : d146266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5765 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5765, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5765, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15104 q ha hb
  have h3 (q : Pattern) (ha : d5721 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5721, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15104 q ha hb
    | true =>
      simp only [d5721, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d5766 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5766, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5766, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5722 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5722, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5722, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5767 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5767, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5767, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5768 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5768, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5768, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5769 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53514 q = 1) (hb : d146266 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro26889 (p : Pattern) (ha : d145178 p = 1) (hb : d146272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145165 q = 1) (hb : d146234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145165, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26881 q ha hb
    | true =>
      simp only [d145165, d146234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d145166 q = 1) (hb : d146235 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145166, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145166, d146235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145167 q = 1) (hb : d146236 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145167, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145167, d146236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145168 q = 1) (hb : d146239 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145168, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26882 q ha hb
    | true =>
      simp only [d145168, d146239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145169 q = 1) (hb : d146240 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145169, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145169, d146240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145170 q = 1) (hb : d146241 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145170, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145170, d146241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145171 q = 1) (hb : d146242 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145171, d146242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145171, d146242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145168 q = 1) (hb : d146267 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145168, d146267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26888 q ha hb
    | true =>
      simp only [d145168, d146267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d145169 q = 1) (hb : d146268 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d145169, d146268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145169, d146268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145170 q = 1) (hb : d146269 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d145170, d146269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145170, d146269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d145176 q = 1) (hb : d146270 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d145176, d146270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d145176, d146270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d145177 q = 1) (hb : d146271 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d145177, d146271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d145177, d146271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d145178 q = 1) (hb : d146272 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d145178, d146272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d145178, d146272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro26890 (p : Pattern) (ha : d145203 p = 1) (hb : d146278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145179 q = 1) (hb : d146273 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145179, d146273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26889 q ha hb
    | true =>
      simp only [d145179, d146273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145180 q = 1) (hb : d146274 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145180, d146274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145180, d146274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145200 q = 1) (hb : d146275 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145200, d146275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145200, d146275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145201 q = 1) (hb : d146276 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145201, d146276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145201, d146276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145202 q = 1) (hb : d146277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145202, d146277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145202, d146277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145203 q = 1) (hb : d146278 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145203, d146278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145203, d146278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26891 (p : Pattern) (ha : d145209 p = 1) (hb : d146284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145193 q = 1) (hb : d146264 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145193, d146264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26885 q ha hb
    | true =>
      simp only [d145193, d146264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26887 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d145198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145199 q = 1) (hb : d146265 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145199, d146265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145199, d146265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d145204 q = 1) (hb : d146279 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145204, d146279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26890 q ha hb
    | true =>
      simp only [d145204, d146279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145205 q = 1) (hb : d146280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145205, d146280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145205, d146280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145206 q = 1) (hb : d146281 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145206, d146281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145206, d146281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145207 q = 1) (hb : d146282 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145207, d146282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145207, d146282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145208 q = 1) (hb : d146283 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145208, d146283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145208, d146283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145209 q = 1) (hb : d146284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145209, d146284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145209, d146284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26892 (p : Pattern) (ha : d145197 p = 1) (hb : d146289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145187 q = 1) (hb : d146258 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d145187, d146258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26886 q ha hb
    | true =>
      simp only [d145187, d146258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145188 q = 1) (hb : d146259 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d145188, d146259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145188, d146259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145194 q = 1) (hb : d146286 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d145194, d146286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145194, d146286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145195 q = 1) (hb : d146287 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d145195, d146287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145195, d146287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145196 q = 1) (hb : d146288 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d145196, d146288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145196, d146288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145197 q = 1) (hb : d146289 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d145197, d146289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145197, d146289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26893 (p : Pattern) (ha : d145216 p = 1) (hb : d146295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145211 q = 1) (hb : d146290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145211, d146290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26892 q ha hb
    | true =>
      simp only [d145211, d146290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145212 q = 1) (hb : d146291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145212, d146291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145212, d146291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145213 q = 1) (hb : d146292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145213, d146292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145213, d146292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145214 q = 1) (hb : d146293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145214, d146293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145214, d146293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145215 q = 1) (hb : d146294 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145215, d146294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145215, d146294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145216 q = 1) (hb : d146295 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145216, d146295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145216, d146295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26894 (p : Pattern) (ha : d145222 p = 1) (hb : d146301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145053 q = 1) (hb : d146117 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145053, d146117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145053, d146117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26854 q ha hb
  have h2 (q : Pattern) (ha : d145054 q = 1) (hb : d146118 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145054, d146118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145054, d146118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145063 q = 1) (hb : d146127 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145063, d146127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26854 q ha hb
    | true =>
      simp only [d145063, d146127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26857 q ha hb
  have h4 (q : Pattern) (ha : d145064 q = 1) (hb : d146128 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145064, d146128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145064, d146128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145065 q = 1) (hb : d146129 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d145065, d146129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145065, d146129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145131 q = 1) (hb : d146202 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145131, d146202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26868 q ha hb
    | true =>
      simp only [d145131, d146202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26875 q ha hb
  have h7 (q : Pattern) (ha : d145144 q = 1) (hb : d146215 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145144, d146215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26876 q ha hb
    | true =>
      simp only [d145144, d146215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26877 q ha hb
  have h8 (q : Pattern) (ha : d145145 q = 1) (hb : d146216 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145145, d146216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145145, d146216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145146 q = 1) (hb : d146217 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d145146, d146217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d145146, d146217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d145147 q = 1) (hb : d146218 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d145147, d146218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145147, d146218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145151 q = 1) (hb : d146222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145151, d146222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145151, d146222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26878 q ha hb
  have h12 (q : Pattern) (ha : d145153 q = 1) (hb : d146224 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145153, d146224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145153, d146224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26879 q ha hb
  have h13 (q : Pattern) (ha : d145154 q = 1) (hb : d146225 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145154, d146225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d145154, d146225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d145155 q = 1) (hb : d146226 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d145155, d146226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d145155, d146226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d145156 q = 1) (hb : d146227 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d145156, d146227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d145156, d146227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d145157 q = 1) (hb : d146228 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d145157, d146228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d145157, d146228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d145210 q = 1) (hb : d146285 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145210, d146285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145210, d146285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26891 q ha hb
  have h18 (q : Pattern) (ha : d145217 q = 1) (hb : d146296 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145217, d146296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145217, d146296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26893 q ha hb
  have h19 (q : Pattern) (ha : d145218 q = 1) (hb : d146297 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145218, d146297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d145218, d146297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d145219 q = 1) (hb : d146298 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d145219, d146298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d145219, d146298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d145220 q = 1) (hb : d146299 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d145220, d146299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d145220, d146299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d145221 q = 1) (hb : d146300 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d145221, d146300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d145221, d146300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d145222 q = 1) (hb : d146301 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d145222, d146301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d145222, d146301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26895 (p : Pattern) (ha : d145228 p = 1) (hb : d146307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145223 q = 1) (hb : d146302 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d145223, d146302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145223, d146302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26894 q ha hb
  have h2 (q : Pattern) (ha : d145224 q = 1) (hb : d146303 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d145224, d146303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145224, d146303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145225 q = 1) (hb : d146304 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d145225, d146304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145225, d146304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145226 q = 1) (hb : d146305 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d145226, d146305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145226, d146305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145227 q = 1) (hb : d146306 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d145227, d146306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145227, d146306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145228 q = 1) (hb : d146307 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d145228, d146307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145228, d146307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26896 (p : Pattern) (ha : d145234 p = 1) (hb : d146313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d144401 q = 1) (hb : d145468 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d144401, d145468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26680 q ha hb
    | true =>
      simp only [d144401, d145468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26705 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144602 q = 1) (hb : d145630 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d144602, d145630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144602, d145630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26751 q ha hb
  have h3 (q : Pattern) (ha : d144603 q = 1) (hb : d145631 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d144603, d145631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d144603, d145631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144810 q = 1) (hb : d145855 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d144810, d145855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144810, d145855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26799 q ha hb
  have h5 (q : Pattern) (ha : d144811 q = 1) (hb : d145856 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d144811, d145856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144811, d145856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144812 q = 1) (hb : d145857 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d144812, d145857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144812, d145857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145019 q = 1) (hb : d146081 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d145019, d146081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145019, d146081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26847 q ha hb
  have h8 (q : Pattern) (ha : d145020 q = 1) (hb : d146082 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d145020, d146082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145020, d146082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145021 q = 1) (hb : d146083 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d145021, d146083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145021, d146083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d145022 q = 1) (hb : d146084 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d145022, d146084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145022, d146084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145229 q = 1) (hb : d146308 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d145229, d146308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145229, d146308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26895 q ha hb
  have h12 (q : Pattern) (ha : d145230 q = 1) (hb : d146309 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d145230, d146309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145230, d146309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d145231 q = 1) (hb : d146310 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d145231, d146310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145231, d146310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d145232 q = 1) (hb : d146311 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d145232, d146311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145232, d146311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d145233 q = 1) (hb : d146312 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d145233, d146312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d145233, d146312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d145234 q = 1) (hb : d146313 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d145234, d146313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d145234, d146313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro26897 (p : Pattern) (ha : d145240 p = 1) (hb : d146319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145235 q = 1) (hb : d146314 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d145235, d146314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26896 q ha hb
    | true =>
      simp only [d145235, d146314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145236 q = 1) (hb : d146315 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d145236, d146315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145236, d146315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145237 q = 1) (hb : d146316 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d145237, d146316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145237, d146316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145238 q = 1) (hb : d146317 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d145238, d146317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145238, d146317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145239 q = 1) (hb : d146318 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d145239, d146318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145239, d146318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145240 q = 1) (hb : d146319 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d145240, d146319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145240, d146319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26898 (p : Pattern) (ha : d145246 p = 1) (hb : d146325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145241 q = 1) (hb : d146320 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d145241, d146320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26897 q ha hb
    | true =>
      simp only [d145241, d146320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145242 q = 1) (hb : d146321 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d145242, d146321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145242, d146321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145243 q = 1) (hb : d146322 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d145243, d146322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145243, d146322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145244 q = 1) (hb : d146323 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d145244, d146323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145244, d146323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145245 q = 1) (hb : d146324 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d145245, d146324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145245, d146324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145246 q = 1) (hb : d146325 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d145246, d146325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145246, d146325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26899 (p : Pattern) (ha : d145252 p = 1) (hb : d146331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145247 q = 1) (hb : d146326 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d145247, d146326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26898 q ha hb
    | true =>
      simp only [d145247, d146326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145248 q = 1) (hb : d146327 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d145248, d146327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145248, d146327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145249 q = 1) (hb : d146328 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d145249, d146328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145249, d146328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145250 q = 1) (hb : d146329 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d145250, d146329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145250, d146329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145251 q = 1) (hb : d146330 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d145251, d146330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145251, d146330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145252 q = 1) (hb : d146331 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d145252, d146331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145252, d146331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26900 (p : Pattern) (ha : d145258 p = 1) (hb : d146337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145253 q = 1) (hb : d146332 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d145253, d146332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26899 q ha hb
    | true =>
      simp only [d145253, d146332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145254 q = 1) (hb : d146333 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d145254, d146333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145254, d146333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145255 q = 1) (hb : d146334 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d145255, d146334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145255, d146334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145256 q = 1) (hb : d146335 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d145256, d146335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145256, d146335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145257 q = 1) (hb : d146336 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d145257, d146336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145257, d146336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145258 q = 1) (hb : d146337 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d145258, d146337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145258, d146337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26901 (p : Pattern) (ha : d145264 p = 1) (hb : d146343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145259 q = 1) (hb : d146338 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d145259, d146338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26900 q ha hb
    | true =>
      simp only [d145259, d146338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145260 q = 1) (hb : d146339 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d145260, d146339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145260, d146339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145261 q = 1) (hb : d146340 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d145261, d146340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145261, d146340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145262 q = 1) (hb : d146341 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d145262, d146341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145262, d146341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145263 q = 1) (hb : d146342 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d145263, d146342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145263, d146342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145264 q = 1) (hb : d146343 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d145264, d146343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145264, d146343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26902 (p : Pattern) (ha : d145270 p = 1) (hb : d146349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145265 q = 1) (hb : d146344 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d145265, d146344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26901 q ha hb
    | true =>
      simp only [d145265, d146344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145266 q = 1) (hb : d146345 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d145266, d146345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145266, d146345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145267 q = 1) (hb : d146346 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d145267, d146346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145267, d146346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145268 q = 1) (hb : d146347 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d145268, d146347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145268, d146347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145269 q = 1) (hb : d146348 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d145269, d146348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145269, d146348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145270 q = 1) (hb : d146349 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d145270, d146349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145270, d146349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26903 (p : Pattern) (ha : d145276 p = 1) (hb : d146355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145271 q = 1) (hb : d146350 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d145271, d146350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26902 q ha hb
    | true =>
      simp only [d145271, d146350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145272 q = 1) (hb : d146351 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d145272, d146351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145272, d146351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145273 q = 1) (hb : d146352 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d145273, d146352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145273, d146352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145274 q = 1) (hb : d146353 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d145274, d146353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145274, d146353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145275 q = 1) (hb : d146354 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d145275, d146354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145275, d146354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145276 q = 1) (hb : d146355 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d145276, d146355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145276, d146355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26904 (p : Pattern) (ha : d53647 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26365 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26366 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26384 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26385 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
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
theorem andIntro26905 (p : Pattern) (ha : d109112 p = 1) (hb : d142666 p = 1) : d120334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10668 q = 1) (hb : d142666 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26376 q ha hb
    | true =>
      simp only [d10668, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26357 q ha hb
  have h2 (q : Pattern) (ha : d10722 q = 1) (hb : d142666 q = 1) : d120139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10722, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10723 q = 1) (hb : d142666 q = 1) : d120140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10723, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10724 q = 1) (hb : d142666 q = 1) : d120141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10725 q = 1) (hb : d142666 q = 1) : d120142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109112 q = 1) (hb : d142666 q = 1) : d120334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109112, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109112, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26906 (p : Pattern) (ha : d109122 p = 1) (hb : d142666 p = 1) : d120378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10698 q = 1) (hb : d142666 q = 1) : d120115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26381 q ha hb
    | true =>
      simp only [d10698, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26362 q ha hb
  have h2 (q : Pattern) (ha : d109118 q = 1) (hb : d142666 q = 1) : d120374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109118, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109118, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109119 q = 1) (hb : d142666 q = 1) : d120375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109119, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109119, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109120 q = 1) (hb : d142666 q = 1) : d120376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109120, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109120, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109121 q = 1) (hb : d142666 q = 1) : d120377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109121, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109121, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109122 q = 1) (hb : d142666 q = 1) : d120378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109122, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109122, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26907 (p : Pattern) (ha : d109128 p = 1) (hb : d142666 p = 1) : d121355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10727 q = 1) (hb : d142666 q = 1) : d120144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26386 q ha hb
    | true =>
      simp only [d10727, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26387 q ha hb
  have h2 (q : Pattern) (ha : d10728 q = 1) (hb : d142666 q = 1) : d120145 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10728, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109110 q = 1) (hb : d142666 q = 1) : d121345 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109110, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109110, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109111 q = 1) (hb : d142666 q = 1) : d121346 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109111, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109111, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109113 q = 1) (hb : d142666 q = 1) : d120335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109113, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109113, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26905 q ha hb
  have h6 (q : Pattern) (ha : d109114 q = 1) (hb : d142666 q = 1) : d121347 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109114, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109114, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109115 q = 1) (hb : d142666 q = 1) : d121348 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109115, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109115, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109116 q = 1) (hb : d142666 q = 1) : d121349 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109116, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109116, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109117 q = 1) (hb : d142666 q = 1) : d121350 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109117, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109117, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109123 q = 1) (hb : d142666 q = 1) : d120379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109123, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109123, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26906 q ha hb
  have h11 (q : Pattern) (ha : d109124 q = 1) (hb : d142666 q = 1) : d121351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109124, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109124, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109125 q = 1) (hb : d142666 q = 1) : d121352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109125, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109125, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109126 q = 1) (hb : d142666 q = 1) : d121353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109126, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109126, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109127 q = 1) (hb : d142666 q = 1) : d121354 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109127, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109127, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109128 q = 1) (hb : d142666 q = 1) : d121355 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109128, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109128, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26908 (p : Pattern) (ha : d109134 p = 1) (hb : d142666 p = 1) : d121361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26904 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109129 q = 1) (hb : d142666 q = 1) : d121356 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109129, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109129, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26907 q ha hb
  have h7 (q : Pattern) (ha : d109130 q = 1) (hb : d142666 q = 1) : d121357 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109130, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109130, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109131 q = 1) (hb : d142666 q = 1) : d121358 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109131, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109131, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109132 q = 1) (hb : d142666 q = 1) : d121359 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109132, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109132, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109133 q = 1) (hb : d142666 q = 1) : d121360 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109133, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109133, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109134 q = 1) (hb : d142666 q = 1) : d121361 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109134, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109134, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26909 (p : Pattern) (ha : d109137 p = 1) (hb : d142666 p = 1) : d146358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10890 q = 1) (hb : d142666 q = 1) : d145297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26414 q ha hb
    | true =>
      simp only [d10890, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26415 q ha hb
  have h2 (q : Pattern) (ha : d10891 q = 1) (hb : d142666 q = 1) : d145353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d145353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10891, d145353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10892 q = 1) (hb : d142666 q = 1) : d145354 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d145354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10892, d145354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10893 q = 1) (hb : d142666 q = 1) : d145355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d145355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d145355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10894 q = 1) (hb : d142666 q = 1) : d145356 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d145356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d145356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109137 q = 1) (hb : d142666 q = 1) : d146358 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109137, d146358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109137, d146358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26910 (p : Pattern) (ha : d109148 p = 1) (hb : d142666 p = 1) : d146368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109143 q = 1) (hb : d142666 q = 1) : d145328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109143, d145328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26444 q ha hb
    | true =>
      simp only [d109143, d145328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26421 q ha hb
  have h2 (q : Pattern) (ha : d109144 q = 1) (hb : d142666 q = 1) : d146364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109144, d146364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109144, d146364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109145 q = 1) (hb : d142666 q = 1) : d146365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109145, d146365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109145, d146365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109146 q = 1) (hb : d142666 q = 1) : d146366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109146, d146366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109146, d146366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109147 q = 1) (hb : d142666 q = 1) : d146367 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109147, d146367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109147, d146367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109148 q = 1) (hb : d142666 q = 1) : d146368 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109148, d146368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109148, d146368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26911 (p : Pattern) (ha : d109154 p = 1) (hb : d142666 p = 1) : d146374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10896 q = 1) (hb : d142666 q = 1) : d145358 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d145358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26413 q ha hb
    | true =>
      simp only [d10896, d145358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26416 q ha hb
  have h2 (q : Pattern) (ha : d10897 q = 1) (hb : d142666 q = 1) : d145359 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d145359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10897, d145359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109135 q = 1) (hb : d142666 q = 1) : d146356 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109135, d146356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109135, d146356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109136 q = 1) (hb : d142666 q = 1) : d146357 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109136, d146357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109136, d146357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109138 q = 1) (hb : d142666 q = 1) : d146359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109138, d146359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109138, d146359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26909 q ha hb
  have h6 (q : Pattern) (ha : d109139 q = 1) (hb : d142666 q = 1) : d146360 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109139, d146360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109139, d146360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109140 q = 1) (hb : d142666 q = 1) : d146361 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109140, d146361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109140, d146361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109141 q = 1) (hb : d142666 q = 1) : d146362 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109141, d146362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109141, d146362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109142 q = 1) (hb : d142666 q = 1) : d146363 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109142, d146363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109142, d146363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109149 q = 1) (hb : d142666 q = 1) : d146369 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109149, d146369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109149, d146369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26910 q ha hb
  have h11 (q : Pattern) (ha : d109150 q = 1) (hb : d142666 q = 1) : d146370 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109150, d146370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109150, d146370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109151 q = 1) (hb : d142666 q = 1) : d146371 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109151, d146371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109151, d146371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109152 q = 1) (hb : d142666 q = 1) : d146372 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109152, d146372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109152, d146372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109153 q = 1) (hb : d142666 q = 1) : d146373 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109153, d146373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109153, d146373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109154 q = 1) (hb : d142666 q = 1) : d146374 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109154, d146374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109154, d146374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26912 (p : Pattern) (ha : d109160 p = 1) (hb : d142666 p = 1) : d146380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109155 q = 1) (hb : d142666 q = 1) : d146375 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109155, d146375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109155, d146375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26911 q ha hb
  have h2 (q : Pattern) (ha : d109156 q = 1) (hb : d142666 q = 1) : d146376 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109156, d146376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109156, d146376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109157 q = 1) (hb : d142666 q = 1) : d146377 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109157, d146377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109157, d146377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109158 q = 1) (hb : d142666 q = 1) : d146378 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109158, d146378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109158, d146378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109159 q = 1) (hb : d142666 q = 1) : d146379 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109159, d146379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109159, d146379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109160 q = 1) (hb : d142666 q = 1) : d146380 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109160, d146380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109160, d146380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26913 (p : Pattern) (ha : d109164 p = 1) (hb : d142666 p = 1) : d146384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11130 q = 1) (hb : d142666 q = 1) : d145487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d145487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26456 q ha hb
    | true =>
      simp only [d11130, d145487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26457 q ha hb
  have h2 (q : Pattern) (ha : d11131 q = 1) (hb : d142666 q = 1) : d145488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d145488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11131, d145488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11132 q = 1) (hb : d142666 q = 1) : d145489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d145489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11132, d145489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11133 q = 1) (hb : d142666 q = 1) : d145490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d145490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d145490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11134 q = 1) (hb : d142666 q = 1) : d145491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d145491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d145491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109164 q = 1) (hb : d142666 q = 1) : d146384 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109164, d146384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109164, d146384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26914 (p : Pattern) (ha : d109175 p = 1) (hb : d142666 p = 1) : d146395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109170 q = 1) (hb : d142666 q = 1) : d146390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109170, d146390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26490 q ha hb
    | true =>
      simp only [d109170, d146390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26464 q ha hb
  have h2 (q : Pattern) (ha : d109171 q = 1) (hb : d142666 q = 1) : d146391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109171, d146391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109171, d146391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109172 q = 1) (hb : d142666 q = 1) : d146392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109172, d146392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109172, d146392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109173 q = 1) (hb : d142666 q = 1) : d146393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109173, d146393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109173, d146393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109174 q = 1) (hb : d142666 q = 1) : d146394 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109174, d146394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109174, d146394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109175 q = 1) (hb : d142666 q = 1) : d146395 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109175, d146395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109175, d146395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26915 (p : Pattern) (ha : d109181 p = 1) (hb : d142666 p = 1) : d146401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11136 q = 1) (hb : d142666 q = 1) : d145493 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d145493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26455 q ha hb
    | true =>
      simp only [d11136, d145493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26458 q ha hb
  have h2 (q : Pattern) (ha : d11137 q = 1) (hb : d142666 q = 1) : d145494 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d145494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11137, d145494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109162 q = 1) (hb : d142666 q = 1) : d146382 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109162, d146382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109162, d146382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109163 q = 1) (hb : d142666 q = 1) : d146383 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109163, d146383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109163, d146383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109165 q = 1) (hb : d142666 q = 1) : d146385 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109165, d146385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109165, d146385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26913 q ha hb
  have h6 (q : Pattern) (ha : d109166 q = 1) (hb : d142666 q = 1) : d146386 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109166, d146386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109166, d146386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109167 q = 1) (hb : d142666 q = 1) : d146387 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109167, d146387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109167, d146387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109168 q = 1) (hb : d142666 q = 1) : d146388 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109168, d146388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109168, d146388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109169 q = 1) (hb : d142666 q = 1) : d146389 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109169, d146389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109169, d146389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109176 q = 1) (hb : d142666 q = 1) : d146396 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109176, d146396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109176, d146396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26914 q ha hb
  have h11 (q : Pattern) (ha : d109177 q = 1) (hb : d142666 q = 1) : d146397 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109177, d146397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109177, d146397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109178 q = 1) (hb : d142666 q = 1) : d146398 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109178, d146398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109178, d146398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109179 q = 1) (hb : d142666 q = 1) : d146399 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109179, d146399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109179, d146399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109180 q = 1) (hb : d142666 q = 1) : d146400 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109180, d146400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109180, d146400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109181 q = 1) (hb : d142666 q = 1) : d146401 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109181, d146401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109181, d146401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26916 (p : Pattern) (ha : d109187 p = 1) (hb : d142666 p = 1) : d146407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109182 q = 1) (hb : d142666 q = 1) : d146402 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109182, d146402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109182, d146402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26915 q ha hb
  have h2 (q : Pattern) (ha : d109183 q = 1) (hb : d142666 q = 1) : d146403 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109183, d146403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109183, d146403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109184 q = 1) (hb : d142666 q = 1) : d146404 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109184, d146404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109184, d146404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109185 q = 1) (hb : d142666 q = 1) : d146405 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109185, d146405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109185, d146405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109186 q = 1) (hb : d142666 q = 1) : d146406 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109186, d146406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109186, d146406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109187 q = 1) (hb : d142666 q = 1) : d146407 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109187, d146407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109187, d146407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26917 (p : Pattern) (ha : d109192 p = 1) (hb : d142666 p = 1) : d146412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11400 q = 1) (hb : d142666 q = 1) : d145668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d145668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26504 q ha hb
    | true =>
      simp only [d11400, d145668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26505 q ha hb
  have h2 (q : Pattern) (ha : d11401 q = 1) (hb : d142666 q = 1) : d145669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d145669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11401, d145669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11402 q = 1) (hb : d142666 q = 1) : d145670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d145670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11402, d145670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11403 q = 1) (hb : d142666 q = 1) : d145671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d145671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d145671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11404 q = 1) (hb : d142666 q = 1) : d145672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d145672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d145672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109192 q = 1) (hb : d142666 q = 1) : d146412 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109192, d146412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109192, d146412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26918 (p : Pattern) (ha : d109203 p = 1) (hb : d142666 p = 1) : d146423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109198 q = 1) (hb : d142666 q = 1) : d146418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109198, d146418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26538 q ha hb
    | true =>
      simp only [d109198, d146418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26512 q ha hb
  have h2 (q : Pattern) (ha : d109199 q = 1) (hb : d142666 q = 1) : d146419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109199, d146419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109199, d146419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109200 q = 1) (hb : d142666 q = 1) : d146420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109200, d146420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109200, d146420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109201 q = 1) (hb : d142666 q = 1) : d146421 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109201, d146421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109201, d146421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109202 q = 1) (hb : d142666 q = 1) : d146422 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109202, d146422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109202, d146422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109203 q = 1) (hb : d142666 q = 1) : d146423 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109203, d146423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109203, d146423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26919 (p : Pattern) (ha : d109209 p = 1) (hb : d142666 p = 1) : d146429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11406 q = 1) (hb : d142666 q = 1) : d145674 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d145674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26503 q ha hb
    | true =>
      simp only [d11406, d145674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26506 q ha hb
  have h2 (q : Pattern) (ha : d11407 q = 1) (hb : d142666 q = 1) : d145675 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d145675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11407, d145675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109190 q = 1) (hb : d142666 q = 1) : d146410 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109190, d146410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109190, d146410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109191 q = 1) (hb : d142666 q = 1) : d146411 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109191, d146411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109191, d146411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109193 q = 1) (hb : d142666 q = 1) : d146413 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109193, d146413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109193, d146413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26917 q ha hb
  have h6 (q : Pattern) (ha : d109194 q = 1) (hb : d142666 q = 1) : d146414 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109194, d146414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109194, d146414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109195 q = 1) (hb : d142666 q = 1) : d146415 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109195, d146415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109195, d146415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109196 q = 1) (hb : d142666 q = 1) : d146416 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109196, d146416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109196, d146416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109197 q = 1) (hb : d142666 q = 1) : d146417 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109197, d146417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109197, d146417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109204 q = 1) (hb : d142666 q = 1) : d146424 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109204, d146424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109204, d146424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26918 q ha hb
  have h11 (q : Pattern) (ha : d109205 q = 1) (hb : d142666 q = 1) : d146425 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109205, d146425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109205, d146425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109206 q = 1) (hb : d142666 q = 1) : d146426 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109206, d146426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109206, d146426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109207 q = 1) (hb : d142666 q = 1) : d146427 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109207, d146427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109207, d146427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109208 q = 1) (hb : d142666 q = 1) : d146428 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109208, d146428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109208, d146428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109209 q = 1) (hb : d142666 q = 1) : d146429 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109209, d146429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109209, d146429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26920 (p : Pattern) (ha : d109215 p = 1) (hb : d142666 p = 1) : d146435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109210 q = 1) (hb : d142666 q = 1) : d146430 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109210, d146430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109210, d146430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26919 q ha hb
  have h2 (q : Pattern) (ha : d109211 q = 1) (hb : d142666 q = 1) : d146431 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109211, d146431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109211, d146431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109212 q = 1) (hb : d142666 q = 1) : d146432 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109212, d146432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109212, d146432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109213 q = 1) (hb : d142666 q = 1) : d146433 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109213, d146433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109213, d146433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109214 q = 1) (hb : d142666 q = 1) : d146434 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109214, d146434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109214, d146434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109215 q = 1) (hb : d142666 q = 1) : d146435 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109215, d146435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109215, d146435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26921 (p : Pattern) (ha : d109221 p = 1) (hb : d142666 p = 1) : d146441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11671 q = 1) (hb : d142666 q = 1) : d145894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d145894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26552 q ha hb
    | true =>
      simp only [d11671, d145894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26553 q ha hb
  have h2 (q : Pattern) (ha : d11672 q = 1) (hb : d142666 q = 1) : d145895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d145895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11672, d145895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11673 q = 1) (hb : d142666 q = 1) : d145896 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d145896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11673, d145896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11674 q = 1) (hb : d142666 q = 1) : d145897 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d145897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d145897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11675 q = 1) (hb : d142666 q = 1) : d145898 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d145898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d145898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109221 q = 1) (hb : d142666 q = 1) : d146441 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109221, d146441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109221, d146441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26922 (p : Pattern) (ha : d109232 p = 1) (hb : d142666 p = 1) : d146452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109227 q = 1) (hb : d142666 q = 1) : d146447 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109227, d146447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26586 q ha hb
    | true =>
      simp only [d109227, d146447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26560 q ha hb
  have h2 (q : Pattern) (ha : d109228 q = 1) (hb : d142666 q = 1) : d146448 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109228, d146448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109228, d146448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109229 q = 1) (hb : d142666 q = 1) : d146449 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109229, d146449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109229, d146449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109230 q = 1) (hb : d142666 q = 1) : d146450 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109230, d146450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109230, d146450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109231 q = 1) (hb : d142666 q = 1) : d146451 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109231, d146451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109231, d146451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109232 q = 1) (hb : d142666 q = 1) : d146452 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109232, d146452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109232, d146452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26923 (p : Pattern) (ha : d109238 p = 1) (hb : d142666 p = 1) : d146458 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11677 q = 1) (hb : d142666 q = 1) : d145900 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d145900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26551 q ha hb
    | true =>
      simp only [d11677, d145900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26554 q ha hb
  have h2 (q : Pattern) (ha : d11678 q = 1) (hb : d142666 q = 1) : d145901 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d145901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11678, d145901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109219 q = 1) (hb : d142666 q = 1) : d146439 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109219, d146439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109219, d146439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109220 q = 1) (hb : d142666 q = 1) : d146440 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109220, d146440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109220, d146440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109222 q = 1) (hb : d142666 q = 1) : d146442 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109222, d146442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109222, d146442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26921 q ha hb
  have h6 (q : Pattern) (ha : d109223 q = 1) (hb : d142666 q = 1) : d146443 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109223, d146443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109223, d146443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109224 q = 1) (hb : d142666 q = 1) : d146444 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109224, d146444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109224, d146444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109225 q = 1) (hb : d142666 q = 1) : d146445 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109225, d146445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109225, d146445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109226 q = 1) (hb : d142666 q = 1) : d146446 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109226, d146446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109226, d146446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109233 q = 1) (hb : d142666 q = 1) : d146453 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109233, d146453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109233, d146453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26922 q ha hb
  have h11 (q : Pattern) (ha : d109234 q = 1) (hb : d142666 q = 1) : d146454 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109234, d146454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109234, d146454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109235 q = 1) (hb : d142666 q = 1) : d146455 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109235, d146455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109235, d146455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109236 q = 1) (hb : d142666 q = 1) : d146456 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109236, d146456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109236, d146456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109237 q = 1) (hb : d142666 q = 1) : d146457 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109237, d146457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109237, d146457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109238 q = 1) (hb : d142666 q = 1) : d146458 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109238, d146458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109238, d146458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26924 (p : Pattern) (ha : d109244 p = 1) (hb : d142666 p = 1) : d146464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109239 q = 1) (hb : d142666 q = 1) : d146459 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109239, d146459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109239, d146459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26923 q ha hb
  have h2 (q : Pattern) (ha : d109240 q = 1) (hb : d142666 q = 1) : d146460 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109240, d146460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109240, d146460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109241 q = 1) (hb : d142666 q = 1) : d146461 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109241, d146461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109241, d146461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109242 q = 1) (hb : d142666 q = 1) : d146462 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109242, d146462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109242, d146462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109243 q = 1) (hb : d142666 q = 1) : d146463 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109243, d146463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109243, d146463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109244 q = 1) (hb : d142666 q = 1) : d146464 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109244, d146464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109244, d146464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26925 (p : Pattern) (ha : d109251 p = 1) (hb : d142666 p = 1) : d146471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11943 q = 1) (hb : d142666 q = 1) : d146121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d146121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26600 q ha hb
    | true =>
      simp only [d11943, d146121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26601 q ha hb
  have h2 (q : Pattern) (ha : d11944 q = 1) (hb : d142666 q = 1) : d146122 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d146122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11944, d146122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11945 q = 1) (hb : d142666 q = 1) : d146123 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d146123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11945, d146123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11946 q = 1) (hb : d142666 q = 1) : d146124 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d146124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d146124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11947 q = 1) (hb : d142666 q = 1) : d146125 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d146125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d146125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109251 q = 1) (hb : d142666 q = 1) : d146471 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109251, d146471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109251, d146471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26926 (p : Pattern) (ha : d109262 p = 1) (hb : d142666 p = 1) : d146482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109257 q = 1) (hb : d142666 q = 1) : d146477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109257, d146477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26634 q ha hb
    | true =>
      simp only [d109257, d146477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26608 q ha hb
  have h2 (q : Pattern) (ha : d109258 q = 1) (hb : d142666 q = 1) : d146478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109258, d146478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109258, d146478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109259 q = 1) (hb : d142666 q = 1) : d146479 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109259, d146479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109259, d146479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109260 q = 1) (hb : d142666 q = 1) : d146480 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109260, d146480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109260, d146480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109261 q = 1) (hb : d142666 q = 1) : d146481 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109261, d146481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109261, d146481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109262 q = 1) (hb : d142666 q = 1) : d146482 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109262, d146482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109262, d146482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26927 (p : Pattern) (ha : d109268 p = 1) (hb : d142666 p = 1) : d146488 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11949 q = 1) (hb : d142666 q = 1) : d146127 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d146127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26599 q ha hb
    | true =>
      simp only [d11949, d146127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26602 q ha hb
  have h2 (q : Pattern) (ha : d11950 q = 1) (hb : d142666 q = 1) : d146128 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d146128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11950, d146128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109249 q = 1) (hb : d142666 q = 1) : d146469 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109249, d146469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109249, d146469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109250 q = 1) (hb : d142666 q = 1) : d146470 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109250, d146470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109250, d146470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109252 q = 1) (hb : d142666 q = 1) : d146472 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109252, d146472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109252, d146472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26925 q ha hb
  have h6 (q : Pattern) (ha : d109253 q = 1) (hb : d142666 q = 1) : d146473 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109253, d146473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109253, d146473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109254 q = 1) (hb : d142666 q = 1) : d146474 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109254, d146474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109254, d146474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109255 q = 1) (hb : d142666 q = 1) : d146475 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109255, d146475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109255, d146475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109256 q = 1) (hb : d142666 q = 1) : d146476 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109256, d146476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109256, d146476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109263 q = 1) (hb : d142666 q = 1) : d146483 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109263, d146483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109263, d146483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26926 q ha hb
  have h11 (q : Pattern) (ha : d109264 q = 1) (hb : d142666 q = 1) : d146484 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109264, d146484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109264, d146484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109265 q = 1) (hb : d142666 q = 1) : d146485 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109265, d146485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109265, d146485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109266 q = 1) (hb : d142666 q = 1) : d146486 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109266, d146486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109266, d146486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109267 q = 1) (hb : d142666 q = 1) : d146487 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109267, d146487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109267, d146487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109268 q = 1) (hb : d142666 q = 1) : d146488 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109268, d146488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109268, d146488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26928 (p : Pattern) (ha : d109274 p = 1) (hb : d142666 p = 1) : d146494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109269 q = 1) (hb : d142666 q = 1) : d146489 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109269, d146489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109269, d146489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26927 q ha hb
  have h2 (q : Pattern) (ha : d109270 q = 1) (hb : d142666 q = 1) : d146490 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109270, d146490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109270, d146490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109271 q = 1) (hb : d142666 q = 1) : d146491 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109271, d146491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109271, d146491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109272 q = 1) (hb : d142666 q = 1) : d146492 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109272, d146492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109272, d146492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109273 q = 1) (hb : d142666 q = 1) : d146493 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109273, d146493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109273, d146493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109274 q = 1) (hb : d142666 q = 1) : d146494 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109274, d146494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109274, d146494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26929 (p : Pattern) (ha : d109280 p = 1) (hb : d142666 p = 1) : d146500 p = 1 := by
  have h0 (q : Pattern) (ha : d109161 q = 1) (hb : d142666 q = 1) : d146381 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109161, d146381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26908 q ha hb
    | true =>
      simp only [d109161, d146381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26912 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d109188 q = 1) (hb : d142666 q = 1) : d146408 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109188, d146408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109188, d146408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26916 q ha hb
  have h3 (q : Pattern) (ha : d109189 q = 1) (hb : d142666 q = 1) : d146409 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109189, d146409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109189, d146409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109216 q = 1) (hb : d142666 q = 1) : d146436 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109216, d146436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109216, d146436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26920 q ha hb
  have h5 (q : Pattern) (ha : d109217 q = 1) (hb : d142666 q = 1) : d146437 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109217, d146437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109217, d146437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109218 q = 1) (hb : d142666 q = 1) : d146438 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109218, d146438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109218, d146438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109245 q = 1) (hb : d142666 q = 1) : d146465 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109245, d146465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109245, d146465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26924 q ha hb
  have h8 (q : Pattern) (ha : d109246 q = 1) (hb : d142666 q = 1) : d146466 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109246, d146466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109246, d146466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109247 q = 1) (hb : d142666 q = 1) : d146467 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109247, d146467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109247, d146467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109248 q = 1) (hb : d142666 q = 1) : d146468 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109248, d146468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109248, d146468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109275 q = 1) (hb : d142666 q = 1) : d146495 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109275, d146495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109275, d146495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26928 q ha hb
  have h12 (q : Pattern) (ha : d109276 q = 1) (hb : d142666 q = 1) : d146496 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109276, d146496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109276, d146496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109277 q = 1) (hb : d142666 q = 1) : d146497 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109277, d146497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109277, d146497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109278 q = 1) (hb : d142666 q = 1) : d146498 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109278, d146498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109278, d146498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109279 q = 1) (hb : d142666 q = 1) : d146499 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109279, d146499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109279, d146499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109280 q = 1) (hb : d142666 q = 1) : d146500 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109280, d146500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109280, d146500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro26930 (p : Pattern) (ha : d109286 p = 1) (hb : d142666 p = 1) : d146506 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109281 q = 1) (hb : d142666 q = 1) : d146501 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109281, d146501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26929 q ha hb
    | true =>
      simp only [d109281, d146501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109282 q = 1) (hb : d142666 q = 1) : d146502 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109282, d146502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109282, d146502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109283 q = 1) (hb : d142666 q = 1) : d146503 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109283, d146503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109283, d146503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109284 q = 1) (hb : d142666 q = 1) : d146504 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109284, d146504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109284, d146504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109285 q = 1) (hb : d142666 q = 1) : d146505 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109285, d146505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109285, d146505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109286 q = 1) (hb : d142666 q = 1) : d146506 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109286, d146506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109286, d146506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26931 (p : Pattern) (ha : d109292 p = 1) (hb : d142666 p = 1) : d146512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109287 q = 1) (hb : d142666 q = 1) : d146507 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109287, d146507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26930 q ha hb
    | true =>
      simp only [d109287, d146507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109288 q = 1) (hb : d142666 q = 1) : d146508 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109288, d146508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109288, d146508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109289 q = 1) (hb : d142666 q = 1) : d146509 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109289, d146509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109289, d146509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109290 q = 1) (hb : d142666 q = 1) : d146510 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109290, d146510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109290, d146510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109291 q = 1) (hb : d142666 q = 1) : d146511 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109291, d146511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109291, d146511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109292 q = 1) (hb : d142666 q = 1) : d146512 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109292, d146512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109292, d146512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26932 (p : Pattern) (ha : d109298 p = 1) (hb : d142666 p = 1) : d146518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109293 q = 1) (hb : d142666 q = 1) : d146513 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109293, d146513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26931 q ha hb
    | true =>
      simp only [d109293, d146513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109294 q = 1) (hb : d142666 q = 1) : d146514 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109294, d146514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109294, d146514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109295 q = 1) (hb : d142666 q = 1) : d146515 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109295, d146515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109295, d146515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109296 q = 1) (hb : d142666 q = 1) : d146516 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109296, d146516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109296, d146516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109297 q = 1) (hb : d142666 q = 1) : d146517 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109297, d146517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109297, d146517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109298 q = 1) (hb : d142666 q = 1) : d146518 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109298, d146518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109298, d146518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26933 (p : Pattern) (ha : d109304 p = 1) (hb : d142666 p = 1) : d146524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109299 q = 1) (hb : d142666 q = 1) : d146519 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109299, d146519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26932 q ha hb
    | true =>
      simp only [d109299, d146519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109300 q = 1) (hb : d142666 q = 1) : d146520 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109300, d146520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109300, d146520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109301 q = 1) (hb : d142666 q = 1) : d146521 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109301, d146521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109301, d146521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109302 q = 1) (hb : d142666 q = 1) : d146522 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109302, d146522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109302, d146522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109303 q = 1) (hb : d142666 q = 1) : d146523 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109303, d146523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109303, d146523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109304 q = 1) (hb : d142666 q = 1) : d146524 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109304, d146524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109304, d146524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26934 (p : Pattern) (ha : d109310 p = 1) (hb : d142666 p = 1) : d146530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109305 q = 1) (hb : d142666 q = 1) : d146525 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109305, d146525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26933 q ha hb
    | true =>
      simp only [d109305, d146525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109306 q = 1) (hb : d142666 q = 1) : d146526 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109306, d146526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109306, d146526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109307 q = 1) (hb : d142666 q = 1) : d146527 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109307, d146527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109307, d146527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109308 q = 1) (hb : d142666 q = 1) : d146528 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109308, d146528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109308, d146528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109309 q = 1) (hb : d142666 q = 1) : d146529 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109309, d146529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109309, d146529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109310 q = 1) (hb : d142666 q = 1) : d146530 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109310, d146530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109310, d146530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26935 (p : Pattern) (ha : d109316 p = 1) (hb : d142666 p = 1) : d146536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109311 q = 1) (hb : d142666 q = 1) : d146531 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109311, d146531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26934 q ha hb
    | true =>
      simp only [d109311, d146531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109312 q = 1) (hb : d142666 q = 1) : d146532 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109312, d146532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109312, d146532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109313 q = 1) (hb : d142666 q = 1) : d146533 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109313, d146533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109313, d146533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109314 q = 1) (hb : d142666 q = 1) : d146534 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109314, d146534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109314, d146534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109315 q = 1) (hb : d142666 q = 1) : d146535 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109315, d146535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109315, d146535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109316 q = 1) (hb : d142666 q = 1) : d146536 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109316, d146536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109316, d146536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26936 (p : Pattern) (ha : d109322 p = 1) (hb : d142666 p = 1) : d146542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109317 q = 1) (hb : d142666 q = 1) : d146537 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109317, d146537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26935 q ha hb
    | true =>
      simp only [d109317, d146537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109318 q = 1) (hb : d142666 q = 1) : d146538 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109318, d146538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109318, d146538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109319 q = 1) (hb : d142666 q = 1) : d146539 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109319, d146539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109319, d146539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109320 q = 1) (hb : d142666 q = 1) : d146540 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109320, d146540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109320, d146540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109321 q = 1) (hb : d142666 q = 1) : d146541 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109321, d146541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109321, d146541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109322 q = 1) (hb : d142666 q = 1) : d146542 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109322, d146542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109322, d146542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26937 (p : Pattern) (ha : d120136 p = 1) (hb : d144212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144188 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144194 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d144207 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d120079 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q ha hb
    | true =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120132 q = 1) (hb : d144208 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d144208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120132, d144208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d144117 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d120133 q = 1) (hb : d144209 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d144209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120133, d144209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120134 q = 1) (hb : d144210 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d144210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120134, d144210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d120135 q = 1) (hb : d144211 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d144211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120135, d144211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120136 q = 1) (hb : d144212 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120136, d144212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120136, d144212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26938 (p : Pattern) (ha : d120143 p = 1) (hb : d144228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144188 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144194 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144207 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d120079 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q ha hb
    | true =>
      simp only [d120079, d144116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120132 q = 1) (hb : d144208 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d144208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120132, d144208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d144117 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d120133 q = 1) (hb : d144209 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d144209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120133, d144209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120134 q = 1) (hb : d144210 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d144210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120134, d144210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d120135 q = 1) (hb : d144211 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d144211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120135, d144211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d144217 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d144221 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d144223 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d120086 q = 1) (hb : d144123 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26653 q ha hb
    | true =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d120139 q = 1) (hb : d144224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d144224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d120139, d144224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d144124 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d120140 q = 1) (hb : d144225 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d144225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d120140, d144225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d120141 q = 1) (hb : d144226 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d144226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120141, d144226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d120142 q = 1) (hb : d144227 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d144227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d120142, d144227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d120143 q = 1) (hb : d144228 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120143, d144228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d120143, d144228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26939 (p : Pattern) (ha : d120334 p = 1) (hb : d144237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144223 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d120086 q = 1) (hb : d144123 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26653 q ha hb
    | true =>
      simp only [d120086, d144123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120139 q = 1) (hb : d144224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d144224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120139, d144224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d144124 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120140 q = 1) (hb : d144225 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d144225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120140, d144225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120141 q = 1) (hb : d144235 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d144235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120141, d144235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120142 q = 1) (hb : d144236 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d144236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120142, d144236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120334 q = 1) (hb : d144237 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120334, d144237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120334, d144237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26940 (p : Pattern) (ha : d120378 p = 1) (hb : d144260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144255 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d120115 q = 1) (hb : d144151 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120115, d144151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26658 q ha hb
    | true =>
      simp only [d120115, d144151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120374 q = 1) (hb : d144256 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120374, d144256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120374, d144256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d144152 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120375 q = 1) (hb : d144257 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120375, d144257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120375, d144257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120376 q = 1) (hb : d144258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120376, d144258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120376, d144258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120377 q = 1) (hb : d144259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120377, d144259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120377, d144259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120378 q = 1) (hb : d144260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120378, d144260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120378, d144260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26941 (p : Pattern) (ha : d121355 p = 1) (hb : d144266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144182 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120144 q = 1) (hb : d144229 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120144, d144229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26937 q ha hb
    | true =>
      simp only [d120144, d144229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26938 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144231 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120145 q = 1) (hb : d144232 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120145, d144232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120145, d144232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121345 q = 1) (hb : d144233 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121345, d144233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121345, d144233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121346 q = 1) (hb : d144234 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121346, d144234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121346, d144234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120335 q = 1) (hb : d144238 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120335, d144238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120335, d144238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26939 q ha hb
  have h8 (q : Pattern) (ha : d121347 q = 1) (hb : d144239 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121347, d144239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d121347, d144239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d121348 q = 1) (hb : d144240 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121348, d144240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d121348, d144240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d121349 q = 1) (hb : d144241 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121349, d144241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d121349, d144241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d121350 q = 1) (hb : d144242 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121350, d144242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d121350, d144242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d120379 q = 1) (hb : d144261 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120379, d144261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120379, d144261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26940 q ha hb
  have h13 (q : Pattern) (ha : d121351 q = 1) (hb : d144262 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121351, d144262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d121351, d144262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d121352 q = 1) (hb : d144263 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121352, d144263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d121352, d144263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d121353 q = 1) (hb : d144264 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121353, d144264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d121353, d144264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d121354 q = 1) (hb : d144265 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121354, d144265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d121354, d144265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d121355 q = 1) (hb : d144266 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d121355, d144266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d121355, d144266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro26942 (p : Pattern) (ha : d121361 p = 1) (hb : d144272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d121356 q = 1) (hb : d144267 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d121356, d144267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121356, d144267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26941 q ha hb
  have h3 (q : Pattern) (ha : d121357 q = 1) (hb : d144268 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d121357, d144268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121357, d144268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d121358 q = 1) (hb : d144269 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d121358, d144269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121358, d144269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d121359 q = 1) (hb : d144270 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d121359, d144270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121359, d144270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121360 q = 1) (hb : d144271 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d121360, d144271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121360, d144271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121361 q = 1) (hb : d144272 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d121361, d144272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121361, d144272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro26943 (p : Pattern) (ha : d144323 p = 1) (hb : d145350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144293 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144299 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d144312 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d144207 q = 1) (hb : d145290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26668 q ha hb
    | true =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q hb ha
  have h5 (q : Pattern) (ha : d144313 q = 1) (hb : d145346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144313, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d144313, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d144319 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d144320 q = 1) (hb : d145347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144320, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144320, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d144321 q = 1) (hb : d145348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144321, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d144321, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144322 q = 1) (hb : d145349 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144322, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144322, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144323 q = 1) (hb : d145350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144323, d145350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144323, d145350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26944 (p : Pattern) (ha : d144342 p = 1) (hb : d145357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144293 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144299 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144207 q = 1) (hb : d145290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26668 q ha hb
    | true =>
      simp only [d144207, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26651 q hb ha
  have h4 (q : Pattern) (ha : d144313 q = 1) (hb : d145346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144313, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d144313, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d144319 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d144320 q = 1) (hb : d145347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144320, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144320, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144321 q = 1) (hb : d145348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144321, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144321, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144322 q = 1) (hb : d145349 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144322, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144322, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144328 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d144332 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d144334 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d144223 q = 1) (hb : d145297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144223, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26672 q ha hb
    | true =>
      simp only [d144223, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26653 q hb ha
  have h13 (q : Pattern) (ha : d144335 q = 1) (hb : d145353 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144335, d145353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d144335, d145353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d144338 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d144339 q = 1) (hb : d145354 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144339, d145354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144339, d145354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d144340 q = 1) (hb : d145355 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144340, d145355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d144340, d145355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d144341 q = 1) (hb : d145356 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144341, d145356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d144341, d145356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d144342 q = 1) (hb : d145357 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144342, d145357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144342, d145357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26945 (p : Pattern) (ha : d144351 p = 1) (hb : d146358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144223 q = 1) (hb : d145297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144223, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26672 q ha hb
    | true =>
      simp only [d144223, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26653 q hb ha
  have h3 (q : Pattern) (ha : d144335 q = 1) (hb : d145353 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144335, d145353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144335, d145353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d144338 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d144339 q = 1) (hb : d145354 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144339, d145354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144339, d145354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144349 q = 1) (hb : d145355 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144349, d145355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144349, d145355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144350 q = 1) (hb : d145356 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144350, d145356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144350, d145356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144351 q = 1) (hb : d146358 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144351, d146358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144351, d146358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26946 (p : Pattern) (ha : d144382 p = 1) (hb : d146368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144371 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144255 q = 1) (hb : d145328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144255, d145328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26677 q ha hb
    | true =>
      simp only [d144255, d145328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26658 q hb ha
  have h3 (q : Pattern) (ha : d144372 q = 1) (hb : d146364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144372, d146364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144372, d146364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d144378 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d144379 q = 1) (hb : d146365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144379, d146365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144379, d146365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144380 q = 1) (hb : d146366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144380, d146366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144380, d146366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144381 q = 1) (hb : d146367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144381, d146367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144381, d146367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144382 q = 1) (hb : d146368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144382, d146368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144382, d146368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26947 (p : Pattern) (ha : d144394 p = 1) (hb : d146374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144287 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144343 q = 1) (hb : d145358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144343, d145358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26943 q ha hb
    | true =>
      simp only [d144343, d145358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26944 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144345 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144346 q = 1) (hb : d145359 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144346, d145359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144346, d145359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d144347 q = 1) (hb : d146356 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144347, d146356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144347, d146356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144348 q = 1) (hb : d146357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144348, d146357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144348, d146357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144352 q = 1) (hb : d146359 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144352, d146359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d144352, d146359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26945 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d144354 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d144355 q = 1) (hb : d146360 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144355, d146360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144355, d146360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d144356 q = 1) (hb : d146361 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144356, d146361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144356, d146361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d144357 q = 1) (hb : d146362 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144357, d146362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144357, d146362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d144358 q = 1) (hb : d146363 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144358, d146363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144358, d146363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d144383 q = 1) (hb : d146369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144383, d146369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d144383, d146369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26946 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d144389 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d144390 q = 1) (hb : d146370 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144390, d146370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144390, d146370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d144391 q = 1) (hb : d146371 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144391, d146371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d144391, d146371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d144392 q = 1) (hb : d146372 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144392, d146372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d144392, d146372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d144393 q = 1) (hb : d146373 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144393, d146373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d144393, d146373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d144394 q = 1) (hb : d146374 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d144394, d146374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d144394, d146374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26948 (p : Pattern) (ha : d144400 p = 1) (hb : d146380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144395 q = 1) (hb : d146375 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d144395, d146375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144395, d146375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26947 q ha hb
  have h2 (q : Pattern) (ha : d144396 q = 1) (hb : d146376 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d144396, d146376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144396, d146376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144397 q = 1) (hb : d146377 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d144397, d146377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144397, d146377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144398 q = 1) (hb : d146378 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d144398, d146378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144398, d146378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144399 q = 1) (hb : d146379 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d144399, d146379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144399, d146379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144400 q = 1) (hb : d146380 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d144400, d146380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144400, d146380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26949 (p : Pattern) (ha : d144485 p = 1) (hb : d145483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144461 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d144474 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d144426 q = 1) (hb : d145478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144426, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26717 q ha hb
    | true =>
      simp only [d144426, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26708 q hb ha
  have h5 (q : Pattern) (ha : d144475 q = 1) (hb : d145479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144475, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d144475, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d144481 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d144482 q = 1) (hb : d145480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144482, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144482, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d144483 q = 1) (hb : d145481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144483, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d144483, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144484 q = 1) (hb : d145482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144484, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144484, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144485 q = 1) (hb : d145483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144485, d145483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144485, d145483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26950 (p : Pattern) (ha : d144506 p = 1) (hb : d145492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144452 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144461 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144474 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144426 q = 1) (hb : d145478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144426, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26717 q ha hb
    | true =>
      simp only [d144426, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26708 q hb ha
  have h4 (q : Pattern) (ha : d144475 q = 1) (hb : d145479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144475, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d144475, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d144481 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d144482 q = 1) (hb : d145480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144482, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144482, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144483 q = 1) (hb : d145481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144483, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144483, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144484 q = 1) (hb : d145482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144484, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144484, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144491 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d144496 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d144498 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d144436 q = 1) (hb : d145487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144436, d145487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26719 q ha hb
    | true =>
      simp only [d144436, d145487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26709 q hb ha
  have h13 (q : Pattern) (ha : d144499 q = 1) (hb : d145488 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144499, d145488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d144499, d145488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d144502 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d144503 q = 1) (hb : d145489 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144503, d145489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144503, d145489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d144504 q = 1) (hb : d145490 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144504, d145490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d144504, d145490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d144505 q = 1) (hb : d145491 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144505, d145491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d144505, d145491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d144506 q = 1) (hb : d145492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144506, d145492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144506, d145492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26951 (p : Pattern) (ha : d144526 p = 1) (hb : d146384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144498 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144436 q = 1) (hb : d145487 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144436, d145487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26719 q ha hb
    | true =>
      simp only [d144436, d145487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26709 q hb ha
  have h3 (q : Pattern) (ha : d144499 q = 1) (hb : d145488 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144499, d145488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144499, d145488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d144502 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d144503 q = 1) (hb : d145489 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144503, d145489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144503, d145489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144524 q = 1) (hb : d145490 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144524, d145490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144524, d145490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144525 q = 1) (hb : d145491 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144525, d145491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144525, d145491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144526 q = 1) (hb : d146384 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144526, d146384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144526, d146384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26952 (p : Pattern) (ha : d144582 p = 1) (hb : d146395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144571 q = 1) (hb : d146390 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144571, d146390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26745 q ha hb
    | true =>
      simp only [d144571, d146390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26714 q hb ha
  have h3 (q : Pattern) (ha : d144572 q = 1) (hb : d146391 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144572, d146391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144572, d146391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d144578 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d144579 q = 1) (hb : d146392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144579, d146392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144579, d146392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144580 q = 1) (hb : d146393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144580, d146393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144580, d146393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144581 q = 1) (hb : d146394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144581, d146394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144581, d146394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144582 q = 1) (hb : d146395 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144582, d146395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144582, d146395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26953 (p : Pattern) (ha : d144595 p = 1) (hb : d146401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144507 q = 1) (hb : d145493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144507, d145493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26949 q ha hb
    | true =>
      simp only [d144507, d145493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26950 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144520 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144521 q = 1) (hb : d145494 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144521, d145494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144521, d145494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d144522 q = 1) (hb : d146382 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144522, d146382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144522, d146382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144523 q = 1) (hb : d146383 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144523, d146383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144523, d146383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144527 q = 1) (hb : d146385 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144527, d146385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d144527, d146385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26951 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d144529 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d144530 q = 1) (hb : d146386 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144530, d146386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144530, d146386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d144531 q = 1) (hb : d146387 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144531, d146387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144531, d146387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d144532 q = 1) (hb : d146388 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144532, d146388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144532, d146388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d144533 q = 1) (hb : d146389 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144533, d146389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144533, d146389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d144583 q = 1) (hb : d146396 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144583, d146396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d144583, d146396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26952 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d144590 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d144591 q = 1) (hb : d146397 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144591, d146397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144591, d146397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d144592 q = 1) (hb : d146398 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144592, d146398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d144592, d146398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d144593 q = 1) (hb : d146399 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144593, d146399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d144593, d146399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d144594 q = 1) (hb : d146400 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144594, d146400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d144594, d146400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d144595 q = 1) (hb : d146401 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d144595, d146401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d144595, d146401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26954 (p : Pattern) (ha : d144601 p = 1) (hb : d146407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144596 q = 1) (hb : d146402 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d144596, d146402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144596, d146402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26953 q ha hb
  have h2 (q : Pattern) (ha : d144597 q = 1) (hb : d146403 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d144597, d146403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144597, d146403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144598 q = 1) (hb : d146404 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d144598, d146404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144598, d146404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144599 q = 1) (hb : d146405 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d144599, d146405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144599, d146405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144600 q = 1) (hb : d146406 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d144600, d146406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144600, d146406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144601 q = 1) (hb : d146407 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d144601, d146407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144601, d146407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26955 (p : Pattern) (ha : d144690 p = 1) (hb : d145663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144654 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144663 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d144679 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d144628 q = 1) (hb : d145658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144628, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26756 q ha hb
    | true =>
      simp only [d144628, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26757 q ha hb
  have h5 (q : Pattern) (ha : d144680 q = 1) (hb : d145659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144680, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d144680, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d144686 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d144687 q = 1) (hb : d145660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144687, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144687, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d144688 q = 1) (hb : d145661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144688, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d144688, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144689 q = 1) (hb : d145662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144689, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144689, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144690 q = 1) (hb : d145663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144690, d145663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144690, d145663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26956 (p : Pattern) (ha : d144711 p = 1) (hb : d145673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144654 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144663 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144679 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144628 q = 1) (hb : d145658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144628, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26756 q ha hb
    | true =>
      simp only [d144628, d145658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26757 q ha hb
  have h4 (q : Pattern) (ha : d144680 q = 1) (hb : d145659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144680, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d144680, d145659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d144686 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d144687 q = 1) (hb : d145660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144687, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144687, d145660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144688 q = 1) (hb : d145661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144688, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144688, d145661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144689 q = 1) (hb : d145662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144689, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144689, d145662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144696 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d144701 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d144703 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d144638 q = 1) (hb : d145668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144638, d145668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26759 q ha hb
    | true =>
      simp only [d144638, d145668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26760 q ha hb
  have h13 (q : Pattern) (ha : d144704 q = 1) (hb : d145669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144704, d145669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d144704, d145669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d144707 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d144708 q = 1) (hb : d145670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144708, d145670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144708, d145670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d144709 q = 1) (hb : d145671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144709, d145671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d144709, d145671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d144710 q = 1) (hb : d145672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144710, d145672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d144710, d145672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d144711 q = 1) (hb : d145673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144711, d145673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144711, d145673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26957 (p : Pattern) (ha : d144731 p = 1) (hb : d146412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144703 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144638 q = 1) (hb : d145668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144638, d145668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26759 q ha hb
    | true =>
      simp only [d144638, d145668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26760 q ha hb
  have h3 (q : Pattern) (ha : d144704 q = 1) (hb : d145669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144704, d145669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144704, d145669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d144707 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d144708 q = 1) (hb : d145670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144708, d145670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144708, d145670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144729 q = 1) (hb : d145671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144729, d145671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144729, d145671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144730 q = 1) (hb : d145672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144730, d145672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144730, d145672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144731 q = 1) (hb : d146412 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144731, d146412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144731, d146412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26958 (p : Pattern) (ha : d144790 p = 1) (hb : d146423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144779 q = 1) (hb : d146418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144779, d146418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26791 q ha hb
    | true =>
      simp only [d144779, d146418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26796 q ha hb
  have h3 (q : Pattern) (ha : d144780 q = 1) (hb : d146419 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144780, d146419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144780, d146419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d144786 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d144787 q = 1) (hb : d146420 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144787, d146420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144787, d146420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144788 q = 1) (hb : d146421 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144788, d146421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144788, d146421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144789 q = 1) (hb : d146422 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144789, d146422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144789, d146422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144790 q = 1) (hb : d146423 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144790, d146423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144790, d146423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26959 (p : Pattern) (ha : d144803 p = 1) (hb : d146429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144646 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144712 q = 1) (hb : d145674 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144712, d145674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26955 q ha hb
    | true =>
      simp only [d144712, d145674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26956 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144725 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144726 q = 1) (hb : d145675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144726, d145675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144726, d145675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d144727 q = 1) (hb : d146410 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144727, d146410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144727, d146410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144728 q = 1) (hb : d146411 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144728, d146411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144728, d146411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144732 q = 1) (hb : d146413 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144732, d146413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d144732, d146413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26957 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d144734 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d144735 q = 1) (hb : d146414 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144735, d146414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144735, d146414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d144736 q = 1) (hb : d146415 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144736, d146415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144736, d146415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d144737 q = 1) (hb : d146416 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144737, d146416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144737, d146416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d144738 q = 1) (hb : d146417 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144738, d146417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144738, d146417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d144791 q = 1) (hb : d146424 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144791, d146424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d144791, d146424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26958 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d144798 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d144799 q = 1) (hb : d146425 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144799, d146425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144799, d146425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d144800 q = 1) (hb : d146426 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144800, d146426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d144800, d146426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d144801 q = 1) (hb : d146427 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144801, d146427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d144801, d146427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d144802 q = 1) (hb : d146428 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144802, d146428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d144802, d146428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d144803 q = 1) (hb : d146429 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d144803, d146429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d144803, d146429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26960 (p : Pattern) (ha : d144809 p = 1) (hb : d146435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144804 q = 1) (hb : d146430 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d144804, d146430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144804, d146430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26959 q ha hb
  have h2 (q : Pattern) (ha : d144805 q = 1) (hb : d146431 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d144805, d146431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144805, d146431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144806 q = 1) (hb : d146432 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d144806, d146432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144806, d146432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144807 q = 1) (hb : d146433 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d144807, d146433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144807, d146433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144808 q = 1) (hb : d146434 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d144808, d146434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144808, d146434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144809 q = 1) (hb : d146435 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d144809, d146435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144809, d146435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26961 (p : Pattern) (ha : d144899 p = 1) (hb : d145889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144863 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144872 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d144888 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d144837 q = 1) (hb : d145884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144837, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26804 q ha hb
    | true =>
      simp only [d144837, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26805 q ha hb
  have h5 (q : Pattern) (ha : d144889 q = 1) (hb : d145885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144889, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d144889, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d144895 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d144896 q = 1) (hb : d145886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144896, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144896, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d144897 q = 1) (hb : d145887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144897, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d144897, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d144898 q = 1) (hb : d145888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144898, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144898, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144899 q = 1) (hb : d145889 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144899, d145889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144899, d145889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26962 (p : Pattern) (ha : d144920 p = 1) (hb : d145899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144863 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144888 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144837 q = 1) (hb : d145884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144837, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26804 q ha hb
    | true =>
      simp only [d144837, d145884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26805 q ha hb
  have h4 (q : Pattern) (ha : d144889 q = 1) (hb : d145885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144889, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d144889, d145885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d144895 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d144896 q = 1) (hb : d145886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144896, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144896, d145886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d144897 q = 1) (hb : d145887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144897, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144897, d145887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144898 q = 1) (hb : d145888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144898, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144898, d145888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144905 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d144910 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d144912 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d144847 q = 1) (hb : d145894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144847, d145894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26807 q ha hb
    | true =>
      simp only [d144847, d145894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26808 q ha hb
  have h13 (q : Pattern) (ha : d144913 q = 1) (hb : d145895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144913, d145895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d144913, d145895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d144916 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d144917 q = 1) (hb : d145896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144917, d145896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144917, d145896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d144918 q = 1) (hb : d145897 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144918, d145897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d144918, d145897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d144919 q = 1) (hb : d145898 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144919, d145898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d144919, d145898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d144920 q = 1) (hb : d145899 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144920, d145899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144920, d145899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26963 (p : Pattern) (ha : d144940 p = 1) (hb : d146441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144912 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144847 q = 1) (hb : d145894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144847, d145894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26807 q ha hb
    | true =>
      simp only [d144847, d145894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26808 q ha hb
  have h3 (q : Pattern) (ha : d144913 q = 1) (hb : d145895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144913, d145895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144913, d145895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d144916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d144917 q = 1) (hb : d145896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144917, d145896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144917, d145896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144938 q = 1) (hb : d145897 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144938, d145897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144938, d145897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144939 q = 1) (hb : d145898 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144939, d145898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144939, d145898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144940 q = 1) (hb : d146441 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144940, d146441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144940, d146441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26964 (p : Pattern) (ha : d144999 p = 1) (hb : d146452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144983 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144988 q = 1) (hb : d146447 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144988, d146447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26839 q ha hb
    | true =>
      simp only [d144988, d146447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26844 q ha hb
  have h3 (q : Pattern) (ha : d144989 q = 1) (hb : d146448 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144989, d146448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144989, d146448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d144995 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d144996 q = 1) (hb : d146449 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144996, d146449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144996, d146449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144997 q = 1) (hb : d146450 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144997, d146450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144997, d146450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144998 q = 1) (hb : d146451 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144998, d146451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144998, d146451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144999 q = 1) (hb : d146452 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144999, d146452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144999, d146452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26965 (p : Pattern) (ha : d145012 p = 1) (hb : d146458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144921 q = 1) (hb : d145900 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144921, d145900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26961 q ha hb
    | true =>
      simp only [d144921, d145900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26962 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d144935 q = 1) (hb : d145901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144935, d145901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144935, d145901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d144936 q = 1) (hb : d146439 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144936, d146439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144936, d146439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d144937 q = 1) (hb : d146440 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144937, d146440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144937, d146440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144941 q = 1) (hb : d146442 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144941, d146442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d144941, d146442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26963 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d144943 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d144944 q = 1) (hb : d146443 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144944, d146443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144944, d146443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d144945 q = 1) (hb : d146444 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144945, d146444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144945, d146444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d144946 q = 1) (hb : d146445 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144946, d146445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144946, d146445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d144947 q = 1) (hb : d146446 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144947, d146446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144947, d146446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d145000 q = 1) (hb : d146453 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145000, d146453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d145000, d146453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26964 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d145007 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d145008 q = 1) (hb : d146454 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145008, d146454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d145008, d146454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d145009 q = 1) (hb : d146455 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d145009, d146455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d145009, d146455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d145010 q = 1) (hb : d146456 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d145010, d146456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d145010, d146456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d145011 q = 1) (hb : d146457 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d145011, d146457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d145011, d146457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d145012 q = 1) (hb : d146458 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d145012, d146458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d145012, d146458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26966 (p : Pattern) (ha : d145018 p = 1) (hb : d146464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145013 q = 1) (hb : d146459 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d145013, d146459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145013, d146459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26965 q ha hb
  have h2 (q : Pattern) (ha : d145014 q = 1) (hb : d146460 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d145014, d146460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145014, d146460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145015 q = 1) (hb : d146461 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d145015, d146461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145015, d146461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145016 q = 1) (hb : d146462 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d145016, d146462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145016, d146462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145017 q = 1) (hb : d146463 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d145017, d146463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145017, d146463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145018 q = 1) (hb : d146464 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d145018, d146464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145018, d146464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26967 (p : Pattern) (ha : d145109 p = 1) (hb : d146116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d145073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d145082 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d145098 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d145047 q = 1) (hb : d146111 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145047, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26852 q ha hb
    | true =>
      simp only [d145047, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26853 q ha hb
  have h5 (q : Pattern) (ha : d145099 q = 1) (hb : d146112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145099, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d145099, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d145105 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d145106 q = 1) (hb : d146113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145106, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145106, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d145107 q = 1) (hb : d146114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145107, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d145107, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145108 q = 1) (hb : d146115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145108, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145108, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d145109 q = 1) (hb : d146116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145109, d146116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145109, d146116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26968 (p : Pattern) (ha : d145130 p = 1) (hb : d146126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d145073 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d145082 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d145098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145047 q = 1) (hb : d146111 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145047, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26852 q ha hb
    | true =>
      simp only [d145047, d146111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26853 q ha hb
  have h4 (q : Pattern) (ha : d145099 q = 1) (hb : d146112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145099, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d145099, d146112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d145105 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d145106 q = 1) (hb : d146113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145106, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145106, d146113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d145107 q = 1) (hb : d146114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145107, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145107, d146114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145108 q = 1) (hb : d146115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145108, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145108, d146115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d145115 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d145120 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d145122 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d145057 q = 1) (hb : d146121 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145057, d146121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26855 q ha hb
    | true =>
      simp only [d145057, d146121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26856 q ha hb
  have h13 (q : Pattern) (ha : d145123 q = 1) (hb : d146122 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145123, d146122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d145123, d146122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d145126 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d145127 q = 1) (hb : d146123 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145127, d146123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d145127, d146123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d145128 q = 1) (hb : d146124 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145128, d146124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d145128, d146124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d145129 q = 1) (hb : d146125 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145129, d146125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d145129, d146125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d145130 q = 1) (hb : d146126 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145130, d146126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d145130, d146126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26969 (p : Pattern) (ha : d145150 p = 1) (hb : d146471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d145122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145057 q = 1) (hb : d146121 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145057, d146121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26855 q ha hb
    | true =>
      simp only [d145057, d146121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26856 q ha hb
  have h3 (q : Pattern) (ha : d145123 q = 1) (hb : d146122 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145123, d146122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145123, d146122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d145126 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145127 q = 1) (hb : d146123 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145127, d146123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145127, d146123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d145148 q = 1) (hb : d146124 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145148, d146124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145148, d146124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145149 q = 1) (hb : d146125 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145149, d146125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145149, d146125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145150 q = 1) (hb : d146471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145150, d146471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145150, d146471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26970 (p : Pattern) (ha : d145209 p = 1) (hb : d146482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d145193 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145198 q = 1) (hb : d146477 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d145198, d146477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26887 q ha hb
    | true =>
      simp only [d145198, d146477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26892 q ha hb
  have h3 (q : Pattern) (ha : d145199 q = 1) (hb : d146478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145199, d146478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145199, d146478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d145205 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145206 q = 1) (hb : d146479 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145206, d146479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145206, d146479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d145207 q = 1) (hb : d146480 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145207, d146480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145207, d146480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145208 q = 1) (hb : d146481 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145208, d146481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145208, d146481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145209 q = 1) (hb : d146482 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145209, d146482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145209, d146482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26971 (p : Pattern) (ha : d145222 p = 1) (hb : d146488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d145065 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145131 q = 1) (hb : d146127 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145131, d146127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26967 q ha hb
    | true =>
      simp only [d145131, d146127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26968 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d145144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145145 q = 1) (hb : d146128 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145145, d146128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145145, d146128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145146 q = 1) (hb : d146469 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d145146, d146469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145146, d146469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d145147 q = 1) (hb : d146470 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d145147, d146470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145147, d146470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145151 q = 1) (hb : d146472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145151, d146472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d145151, d146472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26969 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d145153 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d145154 q = 1) (hb : d146473 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145154, d146473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d145154, d146473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d145155 q = 1) (hb : d146474 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d145155, d146474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d145155, d146474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d145156 q = 1) (hb : d146475 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d145156, d146475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d145156, d146475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d145157 q = 1) (hb : d146476 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d145157, d146476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145157, d146476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d145210 q = 1) (hb : d146483 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145210, d146483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d145210, d146483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26970 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d145217 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d145218 q = 1) (hb : d146484 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145218, d146484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d145218, d146484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d145219 q = 1) (hb : d146485 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d145219, d146485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d145219, d146485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d145220 q = 1) (hb : d146486 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d145220, d146486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d145220, d146486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d145221 q = 1) (hb : d146487 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d145221, d146487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d145221, d146487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d145222 q = 1) (hb : d146488 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d145222, d146488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d145222, d146488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26972 (p : Pattern) (ha : d145228 p = 1) (hb : d146494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145223 q = 1) (hb : d146489 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d145223, d146489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145223, d146489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26971 q ha hb
  have h2 (q : Pattern) (ha : d145224 q = 1) (hb : d146490 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d145224, d146490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145224, d146490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d145225 q = 1) (hb : d146491 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d145225, d146491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145225, d146491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145226 q = 1) (hb : d146492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d145226, d146492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145226, d146492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d145227 q = 1) (hb : d146493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d145227, d146493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145227, d146493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145228 q = 1) (hb : d146494 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d145228, d146494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d145228, d146494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26973 (p : Pattern) (ha : d145234 p = 1) (hb : d146500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d144401 q = 1) (hb : d146381 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d144401, d146381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26942 q hb ha
    | true =>
      simp only [d144401, d146381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26948 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144602 q = 1) (hb : d146408 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d144602, d146408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144602, d146408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26954 q ha hb
  have h3 (q : Pattern) (ha : d144603 q = 1) (hb : d146409 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d144603, d146409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d144603, d146409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144810 q = 1) (hb : d146436 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d144810, d146436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144810, d146436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26960 q ha hb
  have h5 (q : Pattern) (ha : d144811 q = 1) (hb : d146437 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d144811, d146437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d144811, d146437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144812 q = 1) (hb : d146438 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d144812, d146438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144812, d146438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145019 q = 1) (hb : d146465 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d145019, d146465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145019, d146465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26966 q ha hb
  have h8 (q : Pattern) (ha : d145020 q = 1) (hb : d146466 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d145020, d146466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145020, d146466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145021 q = 1) (hb : d146467 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d145021, d146467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145021, d146467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d145022 q = 1) (hb : d146468 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d145022, d146468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d145022, d146468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145229 q = 1) (hb : d146495 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d145229, d146495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145229, d146495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26972 q ha hb
  have h12 (q : Pattern) (ha : d145230 q = 1) (hb : d146496 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d145230, d146496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145230, d146496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d145231 q = 1) (hb : d146497 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d145231, d146497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145231, d146497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d145232 q = 1) (hb : d146498 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d145232, d146498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145232, d146498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d145233 q = 1) (hb : d146499 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d145233, d146499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d145233, d146499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d145234 q = 1) (hb : d146500 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d145234, d146500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d145234, d146500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro26974 (p : Pattern) (ha : d145240 p = 1) (hb : d146506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145235 q = 1) (hb : d146501 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d145235, d146501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26973 q ha hb
    | true =>
      simp only [d145235, d146501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145236 q = 1) (hb : d146502 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d145236, d146502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145236, d146502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145237 q = 1) (hb : d146503 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d145237, d146503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145237, d146503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145238 q = 1) (hb : d146504 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d145238, d146504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145238, d146504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145239 q = 1) (hb : d146505 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d145239, d146505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145239, d146505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145240 q = 1) (hb : d146506 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d145240, d146506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145240, d146506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26975 (p : Pattern) (ha : d145246 p = 1) (hb : d146512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145241 q = 1) (hb : d146507 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d145241, d146507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26974 q ha hb
    | true =>
      simp only [d145241, d146507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145242 q = 1) (hb : d146508 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d145242, d146508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145242, d146508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145243 q = 1) (hb : d146509 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d145243, d146509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145243, d146509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145244 q = 1) (hb : d146510 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d145244, d146510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145244, d146510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145245 q = 1) (hb : d146511 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d145245, d146511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145245, d146511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145246 q = 1) (hb : d146512 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d145246, d146512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145246, d146512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26976 (p : Pattern) (ha : d145252 p = 1) (hb : d146518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145247 q = 1) (hb : d146513 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d145247, d146513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26975 q ha hb
    | true =>
      simp only [d145247, d146513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145248 q = 1) (hb : d146514 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d145248, d146514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145248, d146514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145249 q = 1) (hb : d146515 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d145249, d146515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145249, d146515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145250 q = 1) (hb : d146516 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d145250, d146516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145250, d146516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145251 q = 1) (hb : d146517 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d145251, d146517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145251, d146517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145252 q = 1) (hb : d146518 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d145252, d146518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145252, d146518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26977 (p : Pattern) (ha : d145258 p = 1) (hb : d146524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145253 q = 1) (hb : d146519 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d145253, d146519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26976 q ha hb
    | true =>
      simp only [d145253, d146519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145254 q = 1) (hb : d146520 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d145254, d146520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145254, d146520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145255 q = 1) (hb : d146521 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d145255, d146521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145255, d146521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145256 q = 1) (hb : d146522 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d145256, d146522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145256, d146522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145257 q = 1) (hb : d146523 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d145257, d146523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145257, d146523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145258 q = 1) (hb : d146524 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d145258, d146524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145258, d146524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26978 (p : Pattern) (ha : d145264 p = 1) (hb : d146530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145259 q = 1) (hb : d146525 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d145259, d146525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26977 q ha hb
    | true =>
      simp only [d145259, d146525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145260 q = 1) (hb : d146526 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d145260, d146526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145260, d146526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145261 q = 1) (hb : d146527 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d145261, d146527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145261, d146527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145262 q = 1) (hb : d146528 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d145262, d146528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145262, d146528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145263 q = 1) (hb : d146529 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d145263, d146529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145263, d146529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145264 q = 1) (hb : d146530 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d145264, d146530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145264, d146530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26979 (p : Pattern) (ha : d145270 p = 1) (hb : d146536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145265 q = 1) (hb : d146531 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d145265, d146531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26978 q ha hb
    | true =>
      simp only [d145265, d146531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145266 q = 1) (hb : d146532 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d145266, d146532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145266, d146532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145267 q = 1) (hb : d146533 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d145267, d146533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145267, d146533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145268 q = 1) (hb : d146534 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d145268, d146534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145268, d146534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145269 q = 1) (hb : d146535 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d145269, d146535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145269, d146535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145270 q = 1) (hb : d146536 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d145270, d146536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145270, d146536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26980 (p : Pattern) (ha : d145276 p = 1) (hb : d146542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145271 q = 1) (hb : d146537 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d145271, d146537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26979 q ha hb
    | true =>
      simp only [d145271, d146537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d145272 q = 1) (hb : d146538 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d145272, d146538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145272, d146538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d145273 q = 1) (hb : d146539 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d145273, d146539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145273, d146539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d145274 q = 1) (hb : d146540 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d145274, d146540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145274, d146540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d145275 q = 1) (hb : d146541 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d145275, d146541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145275, d146541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d145276 q = 1) (hb : d146542 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d145276, d146542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145276, d146542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26981 (p : Pattern) (ha : d120136 p = 1) (hb : d146547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142757 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d142770 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120132 q = 1) (hb : d146543 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d146543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120132, d146543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d142680 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d120133 q = 1) (hb : d146544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d146544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120133, d146544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120134 q = 1) (hb : d146545 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d146545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120134, d146545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d120135 q = 1) (hb : d146546 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d146546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120135, d146546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120136 q = 1) (hb : d146547 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120136, d146547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120136, d146547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26982 (p : Pattern) (ha : d120143 p = 1) (hb : d146552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142770 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d120132 q = 1) (hb : d146543 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d146543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120132, d146543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d142680 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d120133 q = 1) (hb : d146544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d146544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120133, d146544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120134 q = 1) (hb : d146545 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d146545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120134, d146545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120135 q = 1) (hb : d146546 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d146546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120135, d146546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d142793 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d142797 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d142799 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d120139 q = 1) (hb : d146548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d146548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120139, d146548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d142687 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d120140 q = 1) (hb : d146549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d146549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d120140, d146549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d120141 q = 1) (hb : d146550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d146550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d120141, d146550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d120142 q = 1) (hb : d146551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d146551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d120142, d146551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d120143 q = 1) (hb : d146552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120143, d146552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d120143, d146552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26983 (p : Pattern) (ha : d120334 p = 1) (hb : d146559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142799 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120139 q = 1) (hb : d146548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d146548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120139, d146548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d142687 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120140 q = 1) (hb : d146549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d146549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120140, d146549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120141 q = 1) (hb : d146557 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d146557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120141, d146557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120142 q = 1) (hb : d146558 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d146558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120142, d146558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120334 q = 1) (hb : d146559 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120334, d146559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120334, d146559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26984 (p : Pattern) (ha : d120378 p = 1) (hb : d146569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142833 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d120115 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120374 q = 1) (hb : d146565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120374, d146565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120374, d146565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d142715 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120375 q = 1) (hb : d146566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120375, d146566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120375, d146566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120376 q = 1) (hb : d146567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120376, d146567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120376, d146567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120377 q = 1) (hb : d146568 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120377, d146568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120377, d146568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120378 q = 1) (hb : d146569 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120378, d146569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120378, d146569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26985 (p : Pattern) (ha : d121355 p = 1) (hb : d146575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142745 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120144 q = 1) (hb : d146553 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120144, d146553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26981 q ha hb
    | true =>
      simp only [d120144, d146553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26982 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120145 q = 1) (hb : d146554 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120145, d146554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120145, d146554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121345 q = 1) (hb : d146555 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121345, d146555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121345, d146555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121346 q = 1) (hb : d146556 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121346, d146556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121346, d146556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120335 q = 1) (hb : d146560 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120335, d146560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120335, d146560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26983 q ha hb
  have h8 (q : Pattern) (ha : d121347 q = 1) (hb : d146561 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121347, d146561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d121347, d146561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d121348 q = 1) (hb : d146562 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121348, d146562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d121348, d146562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d121349 q = 1) (hb : d146563 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121349, d146563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d121349, d146563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d121350 q = 1) (hb : d146564 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121350, d146564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d121350, d146564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d120379 q = 1) (hb : d146570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120379, d146570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120379, d146570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26984 q ha hb
  have h13 (q : Pattern) (ha : d121351 q = 1) (hb : d146571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121351, d146571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d121351, d146571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d121352 q = 1) (hb : d146572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121352, d146572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d121352, d146572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d121353 q = 1) (hb : d146573 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121353, d146573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d121353, d146573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d121354 q = 1) (hb : d146574 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121354, d146574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d121354, d146574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d121355 q = 1) (hb : d146575 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d121355, d146575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d121355, d146575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro26986 (p : Pattern) (ha : d121361 p = 1) (hb : d146581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142730 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d121356 q = 1) (hb : d146576 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d121356, d146576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121356, d146576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26985 q ha hb
  have h3 (q : Pattern) (ha : d121357 q = 1) (hb : d146577 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d121357, d146577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121357, d146577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d121358 q = 1) (hb : d146578 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d121358, d146578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121358, d146578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d121359 q = 1) (hb : d146579 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d121359, d146579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121359, d146579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121360 q = 1) (hb : d146580 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d121360, d146580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121360, d146580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121361 q = 1) (hb : d146581 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d121361, d146581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121361, d146581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro26987 (p : Pattern) (ha : d145350 p = 1) (hb : d146586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142884 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142890 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d142903 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d145290 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145346 q = 1) (hb : d146582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145346, d146582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145346, d146582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d142923 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d145347 q = 1) (hb : d146583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145347, d146583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145347, d146583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145348 q = 1) (hb : d146584 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145348, d146584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145348, d146584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145349 q = 1) (hb : d146585 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145349, d146585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145349, d146585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d145350 q = 1) (hb : d146586 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145350, d146586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145350, d146586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26988 (p : Pattern) (ha : d145357 p = 1) (hb : d146591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142884 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142890 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142903 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d145290 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d145346 q = 1) (hb : d146582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145346, d146582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145346, d146582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d142923 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d145347 q = 1) (hb : d146583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145347, d146583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145347, d146583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145348 q = 1) (hb : d146584 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145348, d146584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145348, d146584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145349 q = 1) (hb : d146585 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145349, d146585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145349, d146585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d142932 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d142936 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d142938 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d145297 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d145353 q = 1) (hb : d146587 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145353, d146587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d145353, d146587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d142944 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d145354 q = 1) (hb : d146588 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145354, d146588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d145354, d146588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d145355 q = 1) (hb : d146589 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145355, d146589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d145355, d146589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d145356 q = 1) (hb : d146590 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145356, d146590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d145356, d146590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d145357 q = 1) (hb : d146591 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145357, d146591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d145357, d146591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26989 (p : Pattern) (ha : d146358 p = 1) (hb : d146598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142938 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d145297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145353 q = 1) (hb : d146587 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145353, d146587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145353, d146587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d142944 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145354 q = 1) (hb : d146588 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145354, d146588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145354, d146588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145355 q = 1) (hb : d146596 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145355, d146596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145355, d146596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145356 q = 1) (hb : d146597 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145356, d146597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145356, d146597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146358 q = 1) (hb : d146598 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146358, d146598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146358, d146598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26990 (p : Pattern) (ha : d146368 p = 1) (hb : d146608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142977 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d145328 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146364 q = 1) (hb : d146604 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146364, d146604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146364, d146604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d142997 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146365 q = 1) (hb : d146605 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146365, d146605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146365, d146605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146366 q = 1) (hb : d146606 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146366, d146606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146366, d146606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146367 q = 1) (hb : d146607 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146367, d146607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146367, d146607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146368 q = 1) (hb : d146608 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146368, d146608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146368, d146608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26991 (p : Pattern) (ha : d146374 p = 1) (hb : d146614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142878 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145358 q = 1) (hb : d146592 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145358, d146592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26987 q ha hb
    | true =>
      simp only [d145358, d146592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26988 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142951 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145359 q = 1) (hb : d146593 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145359, d146593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145359, d146593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146356 q = 1) (hb : d146594 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146356, d146594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146356, d146594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146357 q = 1) (hb : d146595 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146357, d146595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146357, d146595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146359 q = 1) (hb : d146599 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146359, d146599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146359, d146599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26989 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d142960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d146360 q = 1) (hb : d146600 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146360, d146600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146360, d146600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146361 q = 1) (hb : d146601 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146361, d146601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146361, d146601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d146362 q = 1) (hb : d146602 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146362, d146602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146362, d146602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d146363 q = 1) (hb : d146603 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146363, d146603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146363, d146603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146369 q = 1) (hb : d146609 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146369, d146609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146369, d146609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26990 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d143008 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d146370 q = 1) (hb : d146610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146370, d146610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146370, d146610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146371 q = 1) (hb : d146611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146371, d146611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d146371, d146611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d146372 q = 1) (hb : d146612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146372, d146612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d146372, d146612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d146373 q = 1) (hb : d146613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146373, d146613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d146373, d146613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d146374 q = 1) (hb : d146614 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d146374, d146614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d146374, d146614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26992 (p : Pattern) (ha : d146380 p = 1) (hb : d146620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146375 q = 1) (hb : d146615 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d146375, d146615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146375, d146615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26991 q ha hb
  have h2 (q : Pattern) (ha : d146376 q = 1) (hb : d146616 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d146376, d146616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146376, d146616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146377 q = 1) (hb : d146617 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d146377, d146617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146377, d146617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146378 q = 1) (hb : d146618 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d146378, d146618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146378, d146618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146379 q = 1) (hb : d146619 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d146379, d146619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146379, d146619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146380 q = 1) (hb : d146620 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d146380, d146620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146380, d146620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26993 (p : Pattern) (ha : d145483 p = 1) (hb : d146626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143071 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d143080 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d143093 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d145478 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145479 q = 1) (hb : d146622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145479, d146622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145479, d146622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d143125 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d145480 q = 1) (hb : d146623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145480, d146623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145480, d146623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145481 q = 1) (hb : d146624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145481, d146624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145481, d146624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145482 q = 1) (hb : d146625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145482, d146625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145482, d146625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d145483 q = 1) (hb : d146626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145483, d146626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145483, d146626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26994 (p : Pattern) (ha : d145492 p = 1) (hb : d146631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d143071 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143080 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d143093 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d145478 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d145479 q = 1) (hb : d146622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145479, d146622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145479, d146622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d143125 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d145480 q = 1) (hb : d146623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145480, d146623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d145480, d146623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145481 q = 1) (hb : d146624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145481, d146624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145481, d146624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145482 q = 1) (hb : d146625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145482, d146625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145482, d146625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d143135 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d143140 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d143142 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d145487 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d145488 q = 1) (hb : d146627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145488, d146627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d145488, d146627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d143149 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d145489 q = 1) (hb : d146628 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145489, d146628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d145489, d146628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d145490 q = 1) (hb : d146629 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145490, d146629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d145490, d146629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d145491 q = 1) (hb : d146630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145491, d146630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d145491, d146630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d145492 q = 1) (hb : d146631 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145492, d146631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d145492, d146631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26995 (p : Pattern) (ha : d146384 p = 1) (hb : d146638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d145487 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145488 q = 1) (hb : d146627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145488, d146627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145488, d146627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d143149 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145489 q = 1) (hb : d146628 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145489, d146628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145489, d146628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d145490 q = 1) (hb : d146636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145490, d146636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145490, d146636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d145491 q = 1) (hb : d146637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145491, d146637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145491, d146637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146384 q = 1) (hb : d146638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146384, d146638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146384, d146638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26996 (p : Pattern) (ha : d146395 p = 1) (hb : d146648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146390 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146391 q = 1) (hb : d146644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146391, d146644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146391, d146644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d143245 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146392 q = 1) (hb : d146645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146392, d146645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146392, d146645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146393 q = 1) (hb : d146646 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146393, d146646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146393, d146646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146394 q = 1) (hb : d146647 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146394, d146647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146394, d146647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146395 q = 1) (hb : d146648 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146395, d146648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146395, d146648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26997 (p : Pattern) (ha : d146401 p = 1) (hb : d146654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d143063 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145493 q = 1) (hb : d146632 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d145493, d146632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26993 q ha hb
    | true =>
      simp only [d145493, d146632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26994 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d143167 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145494 q = 1) (hb : d146633 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d145494, d146633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145494, d146633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146382 q = 1) (hb : d146634 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146382, d146634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146382, d146634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146383 q = 1) (hb : d146635 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146383, d146635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146383, d146635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146385 q = 1) (hb : d146639 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146385, d146639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146385, d146639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26995 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d143176 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d146386 q = 1) (hb : d146640 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146386, d146640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146386, d146640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146387 q = 1) (hb : d146641 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146387, d146641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146387, d146641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d146388 q = 1) (hb : d146642 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146388, d146642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146388, d146642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d146389 q = 1) (hb : d146643 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146389, d146643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146389, d146643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146396 q = 1) (hb : d146649 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146396, d146649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146396, d146649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26996 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d143261 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d146397 q = 1) (hb : d146650 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146397, d146650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146397, d146650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146398 q = 1) (hb : d146651 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146398, d146651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d146398, d146651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d146399 q = 1) (hb : d146652 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146399, d146652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d146399, d146652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d146400 q = 1) (hb : d146653 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146400, d146653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d146400, d146653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d146401 q = 1) (hb : d146654 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d146401, d146654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d146401, d146654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26998 (p : Pattern) (ha : d146407 p = 1) (hb : d146660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146402 q = 1) (hb : d146655 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d146402, d146655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146402, d146655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26997 q ha hb
  have h2 (q : Pattern) (ha : d146403 q = 1) (hb : d146656 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d146403, d146656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146403, d146656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146404 q = 1) (hb : d146657 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d146404, d146657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146404, d146657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146405 q = 1) (hb : d146658 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d146405, d146658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146405, d146658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146406 q = 1) (hb : d146659 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d146406, d146659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146406, d146659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146407 q = 1) (hb : d146660 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d146407, d146660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146407, d146660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26999 (p : Pattern) (ha : d145663 p = 1) (hb : d146667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d143325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d143334 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d143350 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d145658 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145659 q = 1) (hb : d146663 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d145659, d146663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d145659, d146663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d143382 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d145660 q = 1) (hb : d146664 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d145660, d146664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d145660, d146664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d145661 q = 1) (hb : d146665 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d145661, d146665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d145661, d146665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d145662 q = 1) (hb : d146666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d145662, d146666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d145662, d146666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d145663 q = 1) (hb : d146667 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d145663, d146667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d145663, d146667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
end NetHack.Soko22Hazard87
