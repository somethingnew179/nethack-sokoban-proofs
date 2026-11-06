import NetHack.Soko22Hazard87.AndIntroBlocks0095
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro24000 (p : Pattern) (ha : d129641 p = 1) (hb : d131099 p = 1) : d132557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129636 q = 1) (hb : d131099 q = 1) : d132552 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129636, d132552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23999 q ha hb
    | true =>
      simp only [d129636, d132552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129637 q = 1) (hb : d131099 q = 1) : d132553 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129637, d132553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129637, d132553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129638 q = 1) (hb : d131099 q = 1) : d132554 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129638, d132554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129638, d132554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129639 q = 1) (hb : d131099 q = 1) : d132555 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129639, d132555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129639, d132555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129640 q = 1) (hb : d131099 q = 1) : d132556 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129640, d132556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129640, d132556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129641 q = 1) (hb : d131099 q = 1) : d132557 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129641, d132557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129641, d132557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24001 (p : Pattern) (ha : d129647 p = 1) (hb : d131099 p = 1) : d132563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129642 q = 1) (hb : d131099 q = 1) : d132558 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129642, d132558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24000 q ha hb
    | true =>
      simp only [d129642, d132558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129643 q = 1) (hb : d131099 q = 1) : d132559 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129643, d132559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129643, d132559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129644 q = 1) (hb : d131099 q = 1) : d132560 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129644, d132560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129644, d132560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129645 q = 1) (hb : d131099 q = 1) : d132561 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129645, d132561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129645, d132561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129646 q = 1) (hb : d131099 q = 1) : d132562 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129646, d132562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129646, d132562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129647 q = 1) (hb : d131099 q = 1) : d132563 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129647, d132563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129647, d132563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24002 (p : Pattern) (ha : d129653 p = 1) (hb : d131099 p = 1) : d132569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129648 q = 1) (hb : d131099 q = 1) : d132564 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129648, d132564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24001 q ha hb
    | true =>
      simp only [d129648, d132564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129649 q = 1) (hb : d131099 q = 1) : d132565 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129649, d132565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129649, d132565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129650 q = 1) (hb : d131099 q = 1) : d132566 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129650, d132566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129650, d132566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129651 q = 1) (hb : d131099 q = 1) : d132567 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129651, d132567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129651, d132567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129652 q = 1) (hb : d131099 q = 1) : d132568 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129652, d132568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129652, d132568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129653 q = 1) (hb : d131099 q = 1) : d132569 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129653, d132569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129653, d132569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24003 (p : Pattern) (ha : d129659 p = 1) (hb : d131099 p = 1) : d132575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129654 q = 1) (hb : d131099 q = 1) : d132570 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129654, d132570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24002 q ha hb
    | true =>
      simp only [d129654, d132570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129655 q = 1) (hb : d131099 q = 1) : d132571 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129655, d132571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129655, d132571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129656 q = 1) (hb : d131099 q = 1) : d132572 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129656, d132572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129656, d132572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129657 q = 1) (hb : d131099 q = 1) : d132573 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129657, d132573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129657, d132573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129658 q = 1) (hb : d131099 q = 1) : d132574 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129658, d132574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129658, d132574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129659 q = 1) (hb : d131099 q = 1) : d132575 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129659, d132575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129659, d132575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24004 (p : Pattern) (ha : d129665 p = 1) (hb : d131099 p = 1) : d132581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129660 q = 1) (hb : d131099 q = 1) : d132576 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129660, d132576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24003 q ha hb
    | true =>
      simp only [d129660, d132576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129661 q = 1) (hb : d131099 q = 1) : d132577 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129661, d132577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129661, d132577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129662 q = 1) (hb : d131099 q = 1) : d132578 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129662, d132578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129662, d132578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129663 q = 1) (hb : d131099 q = 1) : d132579 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129663, d132579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129663, d132579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129664 q = 1) (hb : d131099 q = 1) : d132580 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129664, d132580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129664, d132580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129665 q = 1) (hb : d131099 q = 1) : d132581 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129665, d132581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129665, d132581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24005 (p : Pattern) (ha : d129671 p = 1) (hb : d131099 p = 1) : d132587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129666 q = 1) (hb : d131099 q = 1) : d132582 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129666, d132582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24004 q ha hb
    | true =>
      simp only [d129666, d132582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129667 q = 1) (hb : d131099 q = 1) : d132583 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129667, d132583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129667, d132583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129668 q = 1) (hb : d131099 q = 1) : d132584 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129668, d132584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129668, d132584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129669 q = 1) (hb : d131099 q = 1) : d132585 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129669, d132585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129669, d132585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129670 q = 1) (hb : d131099 q = 1) : d132586 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129670, d132586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129670, d132586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129671 q = 1) (hb : d131099 q = 1) : d132587 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129671, d132587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129671, d132587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24006 (p : Pattern) (ha : d131163 p = 1) (hb : d132049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131158 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131121 q = 1) (hb : d131985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131121, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23869 q ha hb
    | true =>
      simp only [d131121, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131159 q = 1) (hb : d132045 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131159, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131159, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131122 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131160 q = 1) (hb : d132046 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131160, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131160, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131161 q = 1) (hb : d132047 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131161, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131161, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131162 q = 1) (hb : d132048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131162, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131162, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131163 q = 1) (hb : d132049 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131163, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131163, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24007 (p : Pattern) (ha : d131169 p = 1) (hb : d132393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131164 q = 1) (hb : d132050 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131164, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131164, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24006 q ha hb
  have h2 (q : Pattern) (ha : d131165 q = 1) (hb : d132389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131165, d132389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131165, d132389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131166 q = 1) (hb : d132390 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131166, d132390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131166, d132390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131167 q = 1) (hb : d132391 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131167, d132391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131167, d132391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131168 q = 1) (hb : d132392 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131168, d132392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131168, d132392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131169 q = 1) (hb : d132393 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131169, d132393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131169, d132393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24008 (p : Pattern) (ha : d131211 p = 1) (hb : d132403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131200 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131158 q = 1) (hb : d132008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131158, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23873 q ha hb
    | true =>
      simp only [d131158, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23869 q ha hb
  have h3 (q : Pattern) (ha : d131201 q = 1) (hb : d132399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131201, d132399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131201, d132399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131207 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131208 q = 1) (hb : d132400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131208, d132400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131208, d132400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131209 q = 1) (hb : d132401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131209, d132401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131209, d132401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131210 q = 1) (hb : d132402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131210, d132402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131210, d132402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131211 q = 1) (hb : d132403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131211, d132403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131211, d132403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24009 (p : Pattern) (ha : d131223 p = 1) (hb : d132409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131212 q = 1) (hb : d132404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131212, d132404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131212, d132404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24008 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131218 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131219 q = 1) (hb : d132405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131219, d132405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131219, d132405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131220 q = 1) (hb : d132406 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131220, d132406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131220, d132406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131221 q = 1) (hb : d132407 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131221, d132407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131221, d132407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131222 q = 1) (hb : d132408 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131222, d132408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131222, d132408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131223 q = 1) (hb : d132409 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131223, d132409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131223, d132409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24010 (p : Pattern) (ha : d131229 p = 1) (hb : d132415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131136 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131170 q = 1) (hb : d132394 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131170, d132394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131170, d132394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24007 q ha hb
  have h3 (q : Pattern) (ha : d131171 q = 1) (hb : d132395 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131171, d132395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131171, d132395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131172 q = 1) (hb : d132396 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131172, d132396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131172, d132396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131173 q = 1) (hb : d132397 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131173, d132397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131173, d132397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131174 q = 1) (hb : d132398 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131174, d132398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131174, d132398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131224 q = 1) (hb : d132410 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131224, d132410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131224, d132410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24009 q ha hb
  have h8 (q : Pattern) (ha : d131225 q = 1) (hb : d132411 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131225, d132411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131225, d132411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131226 q = 1) (hb : d132412 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131226, d132412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131226, d132412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131227 q = 1) (hb : d132413 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131227, d132413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131227, d132413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131228 q = 1) (hb : d132414 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131228, d132414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131228, d132414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131229 q = 1) (hb : d132415 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131229, d132415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131229, d132415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro24011 (p : Pattern) (ha : d131296 p = 1) (hb : d132421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131280 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131285 q = 1) (hb : d132416 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131285, d132416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23890 q ha hb
    | true =>
      simp only [d131285, d132416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23893 q ha hb
  have h3 (q : Pattern) (ha : d131286 q = 1) (hb : d132417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131286, d132417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131286, d132417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131292 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131293 q = 1) (hb : d132418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131293, d132418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131293, d132418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131294 q = 1) (hb : d132419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131294, d132419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131294, d132419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131295 q = 1) (hb : d132420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131295, d132420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131295, d132420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131296 q = 1) (hb : d132421 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131296, d132421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131296, d132421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24012 (p : Pattern) (ha : d131309 p = 1) (hb : d132427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131297 q = 1) (hb : d132422 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131297, d132422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131297, d132422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24011 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131305 q = 1) (hb : d132423 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131305, d132423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131305, d132423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131306 q = 1) (hb : d132424 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131306, d132424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131306, d132424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131307 q = 1) (hb : d132425 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131307, d132425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131307, d132425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131308 q = 1) (hb : d132426 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131308, d132426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131308, d132426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131309 q = 1) (hb : d132427 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131309, d132427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131309, d132427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24013 (p : Pattern) (ha : d131315 p = 1) (hb : d132433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131310 q = 1) (hb : d132428 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131310, d132428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131310, d132428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24012 q ha hb
  have h2 (q : Pattern) (ha : d131311 q = 1) (hb : d132429 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131311, d132429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131311, d132429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131312 q = 1) (hb : d132430 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131312, d132430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131312, d132430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131313 q = 1) (hb : d132431 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131313, d132431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131313, d132431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131314 q = 1) (hb : d132432 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131314, d132432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131314, d132432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131315 q = 1) (hb : d132433 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131315, d132433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131315, d132433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24014 (p : Pattern) (ha : d131404 p = 1) (hb : d132440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131388 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131393 q = 1) (hb : d132435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131393, d132435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23904 q ha hb
    | true =>
      simp only [d131393, d132435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23907 q ha hb
  have h3 (q : Pattern) (ha : d131394 q = 1) (hb : d132436 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131394, d132436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131394, d132436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131400 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131401 q = 1) (hb : d132437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131401, d132437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131401, d132437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131402 q = 1) (hb : d132438 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131402, d132438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131402, d132438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131403 q = 1) (hb : d132439 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131403, d132439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131403, d132439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131404 q = 1) (hb : d132440 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131404, d132440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131404, d132440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24015 (p : Pattern) (ha : d131417 p = 1) (hb : d132446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131405 q = 1) (hb : d132441 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131405, d132441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131405, d132441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24014 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131412 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131413 q = 1) (hb : d132442 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131413, d132442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131413, d132442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131414 q = 1) (hb : d132443 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131414, d132443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131414, d132443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131415 q = 1) (hb : d132444 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131415, d132444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131415, d132444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131416 q = 1) (hb : d132445 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131416, d132445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131416, d132445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131417 q = 1) (hb : d132446 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131417, d132446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131417, d132446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24016 (p : Pattern) (ha : d131423 p = 1) (hb : d132452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131418 q = 1) (hb : d132447 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131418, d132447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131418, d132447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24015 q ha hb
  have h2 (q : Pattern) (ha : d131419 q = 1) (hb : d132448 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131419, d132448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131419, d132448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131420 q = 1) (hb : d132449 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131420, d132449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131420, d132449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131421 q = 1) (hb : d132450 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131421, d132450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131421, d132450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131422 q = 1) (hb : d132451 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131422, d132451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131422, d132451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131423 q = 1) (hb : d132452 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131423, d132452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131423, d132452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24017 (p : Pattern) (ha : d131537 p = 1) (hb : d132456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131535 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16444 q = 1) (hb : d127282 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d127282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23912 q ha hb
    | true =>
      simp only [d16444, d127282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23913 q ha hb
  have h3 (q : Pattern) (ha : d19061 q = 1) (hb : d131496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, d131496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19061, d131496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19062 q = 1) (hb : d131497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, d131497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19062, d131497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16447 q = 1) (hb : d127285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d127285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23913 q ha hb
    | true =>
      simp only [d16447, d127285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23911 q ha hb
  have h6 (q : Pattern) (ha : d19063 q = 1) (hb : d131498 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, d131498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19063, d131498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d19064 q = 1) (hb : d131499 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, d131499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19064, d131499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19065 q = 1) (hb : d131500 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, d131500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19065, d131500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16451 q = 1) (hb : d127289 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d127289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23913 q ha hb
    | true =>
      simp only [d16451, d127289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23919 q ha hb
  have h10 (q : Pattern) (ha : d19088 q = 1) (hb : d131523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19088, d131523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19088, d131523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d19089 q = 1) (hb : d131524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19089, d131524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19089, d131524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19090 q = 1) (hb : d131525 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19090, d131525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19090, d131525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d131536 q = 1) (hb : d132455 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131536, d132455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d131536, d132455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d131537 q = 1) (hb : d132456 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131537, d132456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131537, d132456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro24018 (p : Pattern) (ha : d131543 p = 1) (hb : d132462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131538 q = 1) (hb : d132457 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131538, d132457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24017 q ha hb
    | true =>
      simp only [d131538, d132457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131539 q = 1) (hb : d132458 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131539, d132458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131539, d132458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131528 q = 1) (hb : d132180 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131528, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23920 q ha hb
    | true =>
      simp only [d131528, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131529 q = 1) (hb : d132181 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131529, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131529, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131540 q = 1) (hb : d132459 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131540, d132459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131540, d132459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131541 q = 1) (hb : d132460 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131541, d132460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131541, d132460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131542 q = 1) (hb : d132461 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131542, d132461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131542, d132461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131543 q = 1) (hb : d132462 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131543, d132462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131543, d132462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24019 (p : Pattern) (ha : d131572 p = 1) (hb : d132468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131534 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131548 q = 1) (hb : d132463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131548, d132463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24018 q ha hb
    | true =>
      simp only [d131548, d132463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23925 q ha hb
  have h3 (q : Pattern) (ha : d131549 q = 1) (hb : d132464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131549, d132464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131549, d132464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131568 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131569 q = 1) (hb : d132465 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131569, d132465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131569, d132465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131570 q = 1) (hb : d132466 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131570, d132466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131570, d132466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131571 q = 1) (hb : d132467 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131571, d132467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131571, d132467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131572 q = 1) (hb : d132468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131572, d132468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131572, d132468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24020 (p : Pattern) (ha : d131585 p = 1) (hb : d132474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131573 q = 1) (hb : d132469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131573, d132469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131573, d132469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24019 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131580 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131581 q = 1) (hb : d132470 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131581, d132470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131581, d132470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131582 q = 1) (hb : d132471 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131582, d132471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131582, d132471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131583 q = 1) (hb : d132472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131583, d132472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131583, d132472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131584 q = 1) (hb : d132473 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131584, d132473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131584, d132473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131585 q = 1) (hb : d132474 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131585, d132474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131585, d132474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24021 (p : Pattern) (ha : d131591 p = 1) (hb : d132480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131586 q = 1) (hb : d132475 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131586, d132475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131586, d132475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24020 q ha hb
  have h2 (q : Pattern) (ha : d131587 q = 1) (hb : d132476 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131587, d132476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131587, d132476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131588 q = 1) (hb : d132477 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131588, d132477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131588, d132477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131589 q = 1) (hb : d132478 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131589, d132478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131589, d132478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131590 q = 1) (hb : d132479 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131590, d132479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131590, d132479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131591 q = 1) (hb : d132480 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131591, d132480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131591, d132480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24022 (p : Pattern) (ha : d131709 p = 1) (hb : d132485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131707 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16796 q = 1) (hb : d127570 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d127570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23930 q ha hb
    | true =>
      simp only [d16796, d127570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23931 q ha hb
  have h3 (q : Pattern) (ha : d19293 q = 1) (hb : d131665 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, d131665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19293, d131665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19294 q = 1) (hb : d131666 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, d131666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19294, d131666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16799 q = 1) (hb : d127573 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d127573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23931 q ha hb
    | true =>
      simp only [d16799, d127573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23929 q ha hb
  have h6 (q : Pattern) (ha : d19295 q = 1) (hb : d131667 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, d131667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19295, d131667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d19296 q = 1) (hb : d131668 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, d131668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19296, d131668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19297 q = 1) (hb : d131669 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, d131669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19297, d131669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16803 q = 1) (hb : d127577 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d127577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23931 q ha hb
    | true =>
      simp only [d16803, d127577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23937 q ha hb
  have h10 (q : Pattern) (ha : d19323 q = 1) (hb : d131695 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19323, d131695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19323, d131695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d19324 q = 1) (hb : d131696 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19324, d131696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19324, d131696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19325 q = 1) (hb : d131697 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19325, d131697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19325, d131697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d131708 q = 1) (hb : d132484 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131708, d132484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d131708, d132484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d131709 q = 1) (hb : d132485 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131709, d132485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131709, d132485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro24023 (p : Pattern) (ha : d131715 p = 1) (hb : d132491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131710 q = 1) (hb : d132486 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131710, d132486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24022 q ha hb
    | true =>
      simp only [d131710, d132486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131711 q = 1) (hb : d132487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131711, d132487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131711, d132487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131700 q = 1) (hb : d132238 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131700, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23938 q ha hb
    | true =>
      simp only [d131700, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131701 q = 1) (hb : d132239 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131701, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131701, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131712 q = 1) (hb : d132488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131712, d132488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131712, d132488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131713 q = 1) (hb : d132489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131713, d132489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131713, d132489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131714 q = 1) (hb : d132490 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131714, d132490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131714, d132490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131715 q = 1) (hb : d132491 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131715, d132491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131715, d132491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24024 (p : Pattern) (ha : d131744 p = 1) (hb : d132497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131706 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131720 q = 1) (hb : d132492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131720, d132492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24023 q ha hb
    | true =>
      simp only [d131720, d132492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23943 q ha hb
  have h3 (q : Pattern) (ha : d131721 q = 1) (hb : d132493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131721, d132493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131721, d132493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131740 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131741 q = 1) (hb : d132494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131741, d132494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131741, d132494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131742 q = 1) (hb : d132495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131742, d132495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131742, d132495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131743 q = 1) (hb : d132496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131743, d132496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131743, d132496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131744 q = 1) (hb : d132497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131744, d132497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131744, d132497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24025 (p : Pattern) (ha : d131757 p = 1) (hb : d132503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131745 q = 1) (hb : d132498 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131745, d132498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131745, d132498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24024 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131752 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131753 q = 1) (hb : d132499 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131753, d132499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131753, d132499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131754 q = 1) (hb : d132500 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131754, d132500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131754, d132500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131755 q = 1) (hb : d132501 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131755, d132501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131755, d132501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131756 q = 1) (hb : d132502 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131756, d132502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131756, d132502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131757 q = 1) (hb : d132503 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131757, d132503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131757, d132503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24026 (p : Pattern) (ha : d131763 p = 1) (hb : d132509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131758 q = 1) (hb : d132504 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131758, d132504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131758, d132504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24025 q ha hb
  have h2 (q : Pattern) (ha : d131759 q = 1) (hb : d132505 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131759, d132505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131759, d132505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131760 q = 1) (hb : d132506 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131760, d132506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131760, d132506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131761 q = 1) (hb : d132507 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131761, d132507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131761, d132507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131762 q = 1) (hb : d132508 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131762, d132508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131762, d132508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131763 q = 1) (hb : d132509 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131763, d132509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131763, d132509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24027 (p : Pattern) (ha : d131875 p = 1) (hb : d132515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131873 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17162 q = 1) (hb : d127864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d127864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23948 q ha hb
    | true =>
      simp only [d17162, d127864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23949 q ha hb
  have h3 (q : Pattern) (ha : d19525 q = 1) (hb : d131831 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, d131831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19525, d131831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d19526 q = 1) (hb : d131832 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, d131832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19526, d131832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17165 q = 1) (hb : d127867 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d127867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23949 q ha hb
    | true =>
      simp only [d17165, d127867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23947 q ha hb
  have h6 (q : Pattern) (ha : d19527 q = 1) (hb : d131833 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, d131833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19527, d131833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d19528 q = 1) (hb : d131834 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, d131834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19528, d131834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19529 q = 1) (hb : d131835 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, d131835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19529, d131835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17169 q = 1) (hb : d127871 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d127871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23949 q ha hb
    | true =>
      simp only [d17169, d127871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23955 q ha hb
  have h10 (q : Pattern) (ha : d19555 q = 1) (hb : d131861 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19555, d131861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19555, d131861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d19556 q = 1) (hb : d131862 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19556, d131862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19556, d131862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19557 q = 1) (hb : d131863 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19557, d131863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19557, d131863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d131874 q = 1) (hb : d132514 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131874, d132514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d131874, d132514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d131875 q = 1) (hb : d132515 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131875, d132515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131875, d132515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro24028 (p : Pattern) (ha : d131881 p = 1) (hb : d132521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131876 q = 1) (hb : d132516 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131876, d132516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24027 q ha hb
    | true =>
      simp only [d131876, d132516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131877 q = 1) (hb : d132517 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131877, d132517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131877, d132517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131866 q = 1) (hb : d132297 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131866, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23956 q ha hb
    | true =>
      simp only [d131866, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131867 q = 1) (hb : d132298 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131867, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131867, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131878 q = 1) (hb : d132518 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131878, d132518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131878, d132518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131879 q = 1) (hb : d132519 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131879, d132519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131879, d132519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131880 q = 1) (hb : d132520 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131880, d132520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131880, d132520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131881 q = 1) (hb : d132521 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131881, d132521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131881, d132521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24029 (p : Pattern) (ha : d131910 p = 1) (hb : d132527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131886 q = 1) (hb : d132522 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131886, d132522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24028 q ha hb
    | true =>
      simp only [d131886, d132522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23961 q ha hb
  have h3 (q : Pattern) (ha : d131887 q = 1) (hb : d132523 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131887, d132523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131887, d132523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131906 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131907 q = 1) (hb : d132524 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131907, d132524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131907, d132524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131908 q = 1) (hb : d132525 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131908, d132525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131908, d132525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131909 q = 1) (hb : d132526 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131909, d132526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131909, d132526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131910 q = 1) (hb : d132527 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131910, d132527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131910, d132527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24030 (p : Pattern) (ha : d131923 p = 1) (hb : d132533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131911 q = 1) (hb : d132528 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131911, d132528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131911, d132528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24029 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131918 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131919 q = 1) (hb : d132529 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131919, d132529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131919, d132529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131920 q = 1) (hb : d132530 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131920, d132530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131920, d132530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131921 q = 1) (hb : d132531 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131921, d132531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131921, d132531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131922 q = 1) (hb : d132532 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131922, d132532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131922, d132532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131923 q = 1) (hb : d132533 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131923, d132533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131923, d132533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24031 (p : Pattern) (ha : d131929 p = 1) (hb : d132539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131924 q = 1) (hb : d132534 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131924, d132534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131924, d132534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24030 q ha hb
  have h2 (q : Pattern) (ha : d131925 q = 1) (hb : d132535 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131925, d132535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131925, d132535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131926 q = 1) (hb : d132536 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131926, d132536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131926, d132536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131927 q = 1) (hb : d132537 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131927, d132537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131927, d132537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131928 q = 1) (hb : d132538 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131928, d132538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131928, d132538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131929 q = 1) (hb : d132539 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131929, d132539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131929, d132539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24032 (p : Pattern) (ha : d131935 p = 1) (hb : d132545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d131316 q = 1) (hb : d132434 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131316, d132434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24010 q ha hb
    | true =>
      simp only [d131316, d132434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24013 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131424 q = 1) (hb : d132453 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131424, d132453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131424, d132453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24016 q ha hb
  have h3 (q : Pattern) (ha : d131425 q = 1) (hb : d132454 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131425, d132454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131425, d132454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131592 q = 1) (hb : d132481 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131592, d132481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131592, d132481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24021 q ha hb
  have h5 (q : Pattern) (ha : d131593 q = 1) (hb : d132482 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131593, d132482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131593, d132482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131594 q = 1) (hb : d132483 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131594, d132483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131594, d132483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131764 q = 1) (hb : d132510 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131764, d132510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131764, d132510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24026 q ha hb
  have h8 (q : Pattern) (ha : d131765 q = 1) (hb : d132511 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131765, d132511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131765, d132511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131766 q = 1) (hb : d132512 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131766, d132512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131766, d132512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131767 q = 1) (hb : d132513 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131767, d132513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131767, d132513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131930 q = 1) (hb : d132540 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131930, d132540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131930, d132540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24031 q ha hb
  have h12 (q : Pattern) (ha : d131931 q = 1) (hb : d132541 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131931, d132541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131931, d132541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131932 q = 1) (hb : d132542 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131932, d132542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131932, d132542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131933 q = 1) (hb : d132543 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131933, d132543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131933, d132543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131934 q = 1) (hb : d132544 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d131934, d132544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131934, d132544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d131935 q = 1) (hb : d132545 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d131935, d132545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131935, d132545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro24033 (p : Pattern) (ha : d131941 p = 1) (hb : d132551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131936 q = 1) (hb : d132546 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d131936, d132546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24032 q ha hb
    | true =>
      simp only [d131936, d132546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131937 q = 1) (hb : d132547 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d131937, d132547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131937, d132547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131938 q = 1) (hb : d132548 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d131938, d132548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131938, d132548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131939 q = 1) (hb : d132549 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d131939, d132549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131939, d132549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131940 q = 1) (hb : d132550 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d131940, d132550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131940, d132550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131941 q = 1) (hb : d132551 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d131941, d132551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131941, d132551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24034 (p : Pattern) (ha : d131947 p = 1) (hb : d132557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131942 q = 1) (hb : d132552 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d131942, d132552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24033 q ha hb
    | true =>
      simp only [d131942, d132552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131943 q = 1) (hb : d132553 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d131943, d132553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131943, d132553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131944 q = 1) (hb : d132554 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d131944, d132554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131944, d132554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131945 q = 1) (hb : d132555 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d131945, d132555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131945, d132555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131946 q = 1) (hb : d132556 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d131946, d132556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131946, d132556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131947 q = 1) (hb : d132557 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d131947, d132557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131947, d132557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24035 (p : Pattern) (ha : d131953 p = 1) (hb : d132563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131948 q = 1) (hb : d132558 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131948, d132558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24034 q ha hb
    | true =>
      simp only [d131948, d132558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131949 q = 1) (hb : d132559 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131949, d132559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131949, d132559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131950 q = 1) (hb : d132560 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131950, d132560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131950, d132560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131951 q = 1) (hb : d132561 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d131951, d132561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131951, d132561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131952 q = 1) (hb : d132562 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131952, d132562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131952, d132562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131953 q = 1) (hb : d132563 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131953, d132563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131953, d132563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24036 (p : Pattern) (ha : d131959 p = 1) (hb : d132569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131954 q = 1) (hb : d132564 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131954, d132564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24035 q ha hb
    | true =>
      simp only [d131954, d132564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131955 q = 1) (hb : d132565 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d131955, d132565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131955, d132565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131956 q = 1) (hb : d132566 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131956, d132566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131956, d132566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131957 q = 1) (hb : d132567 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131957, d132567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131957, d132567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131958 q = 1) (hb : d132568 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131958, d132568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131958, d132568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131959 q = 1) (hb : d132569 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131959, d132569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131959, d132569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24037 (p : Pattern) (ha : d131965 p = 1) (hb : d132575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131960 q = 1) (hb : d132570 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131960, d132570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24036 q ha hb
    | true =>
      simp only [d131960, d132570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131961 q = 1) (hb : d132571 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131961, d132571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131961, d132571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131962 q = 1) (hb : d132572 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131962, d132572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131962, d132572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131963 q = 1) (hb : d132573 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131963, d132573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131963, d132573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131964 q = 1) (hb : d132574 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131964, d132574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131964, d132574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131965 q = 1) (hb : d132575 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131965, d132575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131965, d132575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24038 (p : Pattern) (ha : d131971 p = 1) (hb : d132581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131966 q = 1) (hb : d132576 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131966, d132576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24037 q ha hb
    | true =>
      simp only [d131966, d132576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131967 q = 1) (hb : d132577 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131967, d132577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131967, d132577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131968 q = 1) (hb : d132578 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131968, d132578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131968, d132578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131969 q = 1) (hb : d132579 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131969, d132579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131969, d132579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131970 q = 1) (hb : d132580 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131970, d132580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131970, d132580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131971 q = 1) (hb : d132581 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131971, d132581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131971, d132581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24039 (p : Pattern) (ha : d131977 p = 1) (hb : d132587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131972 q = 1) (hb : d132582 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131972, d132582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24038 q ha hb
    | true =>
      simp only [d131972, d132582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131973 q = 1) (hb : d132583 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131973, d132583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131973, d132583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131974 q = 1) (hb : d132584 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131974, d132584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131974, d132584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131975 q = 1) (hb : d132585 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131975, d132585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131975, d132585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131976 q = 1) (hb : d132586 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131976, d132586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131976, d132586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131977 q = 1) (hb : d132587 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131977, d132587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131977, d132587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24040 (p : Pattern) (ha : d132049 p = 1) (hb : d132592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18592 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132045 q = 1) (hb : d132588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132045, d132588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132045, d132588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18556 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132046 q = 1) (hb : d132589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132046, d132589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132046, d132589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132047 q = 1) (hb : d132590 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132047, d132590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132047, d132590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132048 q = 1) (hb : d132591 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132048, d132591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132048, d132591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132049 q = 1) (hb : d132592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132049, d132592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132049, d132592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24041 (p : Pattern) (ha : d132393 p = 1) (hb : d132598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132050 q = 1) (hb : d132593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132050, d132593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132050, d132593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24040 q ha hb
  have h2 (q : Pattern) (ha : d132389 q = 1) (hb : d132594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132389, d132594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132389, d132594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132390 q = 1) (hb : d132595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132390, d132595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132390, d132595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132391 q = 1) (hb : d132596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132391, d132596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132391, d132596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132392 q = 1) (hb : d132597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132392, d132597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132392, d132597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132393 q = 1) (hb : d132598 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132393, d132598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132393, d132598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24042 (p : Pattern) (ha : d132403 p = 1) (hb : d132608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18656 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d132008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132399 q = 1) (hb : d132604 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132399, d132604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132399, d132604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18685 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132400 q = 1) (hb : d132605 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132400, d132605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132400, d132605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132401 q = 1) (hb : d132606 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132401, d132606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132401, d132606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132402 q = 1) (hb : d132607 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132402, d132607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132402, d132607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132403 q = 1) (hb : d132608 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132403, d132608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132403, d132608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24043 (p : Pattern) (ha : d132409 p = 1) (hb : d132614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132404 q = 1) (hb : d132609 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132404, d132609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132404, d132609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24042 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18696 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132405 q = 1) (hb : d132610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132405, d132610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132405, d132610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132406 q = 1) (hb : d132611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132406, d132611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132406, d132611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132407 q = 1) (hb : d132612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132407, d132612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132407, d132612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132408 q = 1) (hb : d132613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132408, d132613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132408, d132613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132409 q = 1) (hb : d132614 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132409, d132614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132409, d132614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24044 (p : Pattern) (ha : d132415 p = 1) (hb : d132620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18570 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d132394 q = 1) (hb : d132599 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132394, d132599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132394, d132599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24041 q ha hb
  have h3 (q : Pattern) (ha : d132395 q = 1) (hb : d132600 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132395, d132600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132395, d132600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132396 q = 1) (hb : d132601 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132396, d132601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132396, d132601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132397 q = 1) (hb : d132602 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132397, d132602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132397, d132602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132398 q = 1) (hb : d132603 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132398, d132603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132398, d132603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132410 q = 1) (hb : d132615 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132410, d132615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132410, d132615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24043 q ha hb
  have h8 (q : Pattern) (ha : d132411 q = 1) (hb : d132616 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132411, d132616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132411, d132616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d132412 q = 1) (hb : d132617 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132412, d132617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132412, d132617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d132413 q = 1) (hb : d132618 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132413, d132618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132413, d132618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d132414 q = 1) (hb : d132619 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132414, d132619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132414, d132619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d132415 q = 1) (hb : d132620 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132415, d132620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d132415, d132620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro24045 (p : Pattern) (ha : d132421 p = 1) (hb : d132625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18758 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d132416 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132417 q = 1) (hb : d132621 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132417, d132621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132417, d132621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18802 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132418 q = 1) (hb : d132622 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132418, d132622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132418, d132622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132419 q = 1) (hb : d132623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132419, d132623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132419, d132623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132420 q = 1) (hb : d132624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132420, d132624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132420, d132624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132421 q = 1) (hb : d132625 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132421, d132625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132421, d132625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24046 (p : Pattern) (ha : d132427 p = 1) (hb : d132631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132422 q = 1) (hb : d132626 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132422, d132626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132422, d132626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24045 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18818 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132423 q = 1) (hb : d132627 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132423, d132627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132423, d132627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132424 q = 1) (hb : d132628 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132424, d132628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132424, d132628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132425 q = 1) (hb : d132629 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132425, d132629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132425, d132629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132426 q = 1) (hb : d132630 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132426, d132630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132426, d132630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132427 q = 1) (hb : d132631 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132427, d132631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132427, d132631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24047 (p : Pattern) (ha : d132433 p = 1) (hb : d132637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132428 q = 1) (hb : d132632 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132428, d132632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132428, d132632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24046 q ha hb
  have h2 (q : Pattern) (ha : d132429 q = 1) (hb : d132633 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132429, d132633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132429, d132633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132430 q = 1) (hb : d132634 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132430, d132634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132430, d132634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132431 q = 1) (hb : d132635 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132431, d132635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132431, d132635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132432 q = 1) (hb : d132636 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132432, d132636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132432, d132636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132433 q = 1) (hb : d132637 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132433, d132637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132433, d132637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24048 (p : Pattern) (ha : d132440 p = 1) (hb : d132643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18902 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d132435 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132436 q = 1) (hb : d132639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132436, d132639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132436, d132639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18961 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132437 q = 1) (hb : d132640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132437, d132640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132437, d132640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132438 q = 1) (hb : d132641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132438, d132641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132438, d132641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132439 q = 1) (hb : d132642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132439, d132642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132439, d132642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132440 q = 1) (hb : d132643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132440, d132643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132440, d132643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24049 (p : Pattern) (ha : d132446 p = 1) (hb : d132649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132441 q = 1) (hb : d132644 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132441, d132644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132441, d132644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24048 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18977 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132442 q = 1) (hb : d132645 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132442, d132645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132442, d132645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132443 q = 1) (hb : d132646 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132443, d132646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132443, d132646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132444 q = 1) (hb : d132647 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132444, d132647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132444, d132647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132445 q = 1) (hb : d132648 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132445, d132648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132445, d132648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132446 q = 1) (hb : d132649 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132446, d132649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132446, d132649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24050 (p : Pattern) (ha : d132452 p = 1) (hb : d132655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132447 q = 1) (hb : d132650 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132447, d132650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132447, d132650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24049 q ha hb
  have h2 (q : Pattern) (ha : d132448 q = 1) (hb : d132651 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132448, d132651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132448, d132651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132449 q = 1) (hb : d132652 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132449, d132652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132449, d132652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132450 q = 1) (hb : d132653 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132450, d132653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132450, d132653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132451 q = 1) (hb : d132654 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132451, d132654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132451, d132654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132452 q = 1) (hb : d132655 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132452, d132655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132452, d132655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24051 (p : Pattern) (ha : d132468 p = 1) (hb : d132662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d19099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d132463 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132464 q = 1) (hb : d132658 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132464, d132658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132464, d132658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d19192 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132465 q = 1) (hb : d132659 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132465, d132659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132465, d132659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132466 q = 1) (hb : d132660 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132466, d132660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132466, d132660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132467 q = 1) (hb : d132661 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132467, d132661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132467, d132661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132468 q = 1) (hb : d132662 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132468, d132662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132468, d132662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24052 (p : Pattern) (ha : d132474 p = 1) (hb : d132668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132469 q = 1) (hb : d132663 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132469, d132663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132469, d132663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24051 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19208 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132470 q = 1) (hb : d132664 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132470, d132664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132470, d132664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132471 q = 1) (hb : d132665 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132471, d132665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132471, d132665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132472 q = 1) (hb : d132666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132472, d132666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132472, d132666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132473 q = 1) (hb : d132667 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132473, d132667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132473, d132667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132474 q = 1) (hb : d132668 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132474, d132668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132474, d132668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24053 (p : Pattern) (ha : d132480 p = 1) (hb : d132674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132475 q = 1) (hb : d132669 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132475, d132669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132475, d132669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24052 q ha hb
  have h2 (q : Pattern) (ha : d132476 q = 1) (hb : d132670 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132476, d132670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132476, d132670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132477 q = 1) (hb : d132671 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132477, d132671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132477, d132671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132478 q = 1) (hb : d132672 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132478, d132672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132478, d132672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132479 q = 1) (hb : d132673 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132479, d132673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132479, d132673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132480 q = 1) (hb : d132674 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132480, d132674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132480, d132674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24054 (p : Pattern) (ha : d132497 p = 1) (hb : d132682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d19334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d132492 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132493 q = 1) (hb : d132678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132493, d132678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132493, d132678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d19430 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132494 q = 1) (hb : d132679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132494, d132679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132494, d132679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132495 q = 1) (hb : d132680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132495, d132680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132495, d132680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132496 q = 1) (hb : d132681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132496, d132681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132496, d132681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132497 q = 1) (hb : d132682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132497, d132682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132497, d132682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24055 (p : Pattern) (ha : d132503 p = 1) (hb : d132688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132498 q = 1) (hb : d132683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132498, d132683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132498, d132683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24054 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19446 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132499 q = 1) (hb : d132684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132499, d132684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132499, d132684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132500 q = 1) (hb : d132685 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132500, d132685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132500, d132685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132501 q = 1) (hb : d132686 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132501, d132686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132501, d132686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132502 q = 1) (hb : d132687 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132502, d132687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132502, d132687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132503 q = 1) (hb : d132688 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132503, d132688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132503, d132688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24056 (p : Pattern) (ha : d132509 p = 1) (hb : d132694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132504 q = 1) (hb : d132689 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132504, d132689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132504, d132689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24055 q ha hb
  have h2 (q : Pattern) (ha : d132505 q = 1) (hb : d132690 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132505, d132690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132505, d132690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132506 q = 1) (hb : d132691 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132506, d132691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132506, d132691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132507 q = 1) (hb : d132692 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132507, d132692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132507, d132692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132508 q = 1) (hb : d132693 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132508, d132693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132508, d132693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132509 q = 1) (hb : d132694 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132509, d132694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132509, d132694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24057 (p : Pattern) (ha : d132527 p = 1) (hb : d132703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d19566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d132522 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132523 q = 1) (hb : d132699 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132523, d132699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132523, d132699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d19662 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132524 q = 1) (hb : d132700 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132524, d132700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132524, d132700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132525 q = 1) (hb : d132701 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132525, d132701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132525, d132701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132526 q = 1) (hb : d132702 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132526, d132702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132526, d132702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132527 q = 1) (hb : d132703 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132527, d132703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132527, d132703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24058 (p : Pattern) (ha : d132533 p = 1) (hb : d132709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132528 q = 1) (hb : d132704 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132528, d132704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132528, d132704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24057 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19678 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132529 q = 1) (hb : d132705 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132529, d132705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132529, d132705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132530 q = 1) (hb : d132706 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132530, d132706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132530, d132706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132531 q = 1) (hb : d132707 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132531, d132707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132531, d132707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132532 q = 1) (hb : d132708 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132532, d132708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132532, d132708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132533 q = 1) (hb : d132709 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132533, d132709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132533, d132709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24059 (p : Pattern) (ha : d132539 p = 1) (hb : d132715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132534 q = 1) (hb : d132710 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132534, d132710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132534, d132710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24058 q ha hb
  have h2 (q : Pattern) (ha : d132535 q = 1) (hb : d132711 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132535, d132711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132535, d132711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132536 q = 1) (hb : d132712 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132536, d132712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132536, d132712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132537 q = 1) (hb : d132713 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132537, d132713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132537, d132713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132538 q = 1) (hb : d132714 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132538, d132714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132538, d132714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132539 q = 1) (hb : d132715 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132539, d132715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132539, d132715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24060 (p : Pattern) (ha : d132545 p = 1) (hb : d132721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d132434 q = 1) (hb : d132638 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132434, d132638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24044 q ha hb
    | true =>
      simp only [d132434, d132638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24047 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d132453 q = 1) (hb : d132656 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132453, d132656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132453, d132656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24050 q ha hb
  have h3 (q : Pattern) (ha : d132454 q = 1) (hb : d132657 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132454, d132657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132454, d132657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132481 q = 1) (hb : d132675 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132481, d132675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132481, d132675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24053 q ha hb
  have h5 (q : Pattern) (ha : d132482 q = 1) (hb : d132676 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132482, d132676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132482, d132676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132483 q = 1) (hb : d132677 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132483, d132677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132483, d132677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132510 q = 1) (hb : d132695 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132510, d132695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132510, d132695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24056 q ha hb
  have h8 (q : Pattern) (ha : d132511 q = 1) (hb : d132696 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132511, d132696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132511, d132696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d132512 q = 1) (hb : d132697 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132512, d132697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132512, d132697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d132513 q = 1) (hb : d132698 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d132513, d132698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d132513, d132698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d132540 q = 1) (hb : d132716 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132540, d132716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132540, d132716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24059 q ha hb
  have h12 (q : Pattern) (ha : d132541 q = 1) (hb : d132717 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132541, d132717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132541, d132717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d132542 q = 1) (hb : d132718 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132542, d132718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132542, d132718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d132543 q = 1) (hb : d132719 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d132543, d132719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132543, d132719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d132544 q = 1) (hb : d132720 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d132544, d132720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d132544, d132720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d132545 q = 1) (hb : d132721 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d132545, d132721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d132545, d132721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro24061 (p : Pattern) (ha : d132551 p = 1) (hb : d132727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132546 q = 1) (hb : d132722 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d132546, d132722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24060 q ha hb
    | true =>
      simp only [d132546, d132722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132547 q = 1) (hb : d132723 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d132547, d132723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132547, d132723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132548 q = 1) (hb : d132724 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d132548, d132724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132548, d132724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132549 q = 1) (hb : d132725 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d132549, d132725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132549, d132725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132550 q = 1) (hb : d132726 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d132550, d132726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132550, d132726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132551 q = 1) (hb : d132727 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d132551, d132727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132551, d132727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24062 (p : Pattern) (ha : d132557 p = 1) (hb : d132733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132552 q = 1) (hb : d132728 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d132552, d132728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24061 q ha hb
    | true =>
      simp only [d132552, d132728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132553 q = 1) (hb : d132729 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d132553, d132729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132553, d132729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132554 q = 1) (hb : d132730 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d132554, d132730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132554, d132730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132555 q = 1) (hb : d132731 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d132555, d132731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132555, d132731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132556 q = 1) (hb : d132732 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d132556, d132732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132556, d132732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132557 q = 1) (hb : d132733 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d132557, d132733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132557, d132733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24063 (p : Pattern) (ha : d132563 p = 1) (hb : d132739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132558 q = 1) (hb : d132734 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d132558, d132734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24062 q ha hb
    | true =>
      simp only [d132558, d132734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132559 q = 1) (hb : d132735 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d132559, d132735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132559, d132735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132560 q = 1) (hb : d132736 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d132560, d132736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132560, d132736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132561 q = 1) (hb : d132737 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d132561, d132737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132561, d132737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132562 q = 1) (hb : d132738 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d132562, d132738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132562, d132738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132563 q = 1) (hb : d132739 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d132563, d132739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132563, d132739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24064 (p : Pattern) (ha : d132569 p = 1) (hb : d132745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132564 q = 1) (hb : d132740 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d132564, d132740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24063 q ha hb
    | true =>
      simp only [d132564, d132740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132565 q = 1) (hb : d132741 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d132565, d132741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132565, d132741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132566 q = 1) (hb : d132742 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d132566, d132742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132566, d132742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132567 q = 1) (hb : d132743 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d132567, d132743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132567, d132743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132568 q = 1) (hb : d132744 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d132568, d132744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132568, d132744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132569 q = 1) (hb : d132745 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d132569, d132745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132569, d132745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24065 (p : Pattern) (ha : d132575 p = 1) (hb : d132751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132570 q = 1) (hb : d132746 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d132570, d132746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24064 q ha hb
    | true =>
      simp only [d132570, d132746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132571 q = 1) (hb : d132747 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d132571, d132747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132571, d132747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132572 q = 1) (hb : d132748 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d132572, d132748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132572, d132748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132573 q = 1) (hb : d132749 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d132573, d132749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132573, d132749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132574 q = 1) (hb : d132750 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d132574, d132750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132574, d132750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132575 q = 1) (hb : d132751 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d132575, d132751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132575, d132751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24066 (p : Pattern) (ha : d132581 p = 1) (hb : d132757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132576 q = 1) (hb : d132752 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d132576, d132752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24065 q ha hb
    | true =>
      simp only [d132576, d132752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132577 q = 1) (hb : d132753 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d132577, d132753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132577, d132753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132578 q = 1) (hb : d132754 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d132578, d132754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132578, d132754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132579 q = 1) (hb : d132755 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d132579, d132755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132579, d132755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132580 q = 1) (hb : d132756 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d132580, d132756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132580, d132756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132581 q = 1) (hb : d132757 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d132581, d132757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132581, d132757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24067 (p : Pattern) (ha : d132587 p = 1) (hb : d132763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132582 q = 1) (hb : d132758 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d132582, d132758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24066 q ha hb
    | true =>
      simp only [d132582, d132758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132583 q = 1) (hb : d132759 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d132583, d132759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132583, d132759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132584 q = 1) (hb : d132760 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d132584, d132760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132584, d132760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132585 q = 1) (hb : d132761 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d132585, d132761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132585, d132761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132586 q = 1) (hb : d132762 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d132586, d132762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132586, d132762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132587 q = 1) (hb : d132763 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d132587, d132763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132587, d132763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24068 (p : Pattern) (ha : d74849 p = 1) (hb : d132764 p = 1) : d74849 p = 1 := by
  have h0 (q : Pattern) (ha : d74849 q = 1) (hb : d132764 q = 1) : d74849 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro24069 (p : Pattern) (ha : d53865 p = 1) (hb : d132764 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d53865 q = 1) (hb : d132764 q = 1) : d53865 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro24070 (p : Pattern) (ha : d74831 p = 1) (hb : d132769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d132766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74826 q = 1) (hb : d132768 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74826, d132768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74826, d132768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d132768 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d74827 q = 1) (hb : d132768 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74828 q = 1) (hb : d132768 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d74829 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74829, d132769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74829, d132769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74830 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74831 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h10 p ha hb
theorem andIntro24071 (p : Pattern) (ha : d74837 p = 1) (hb : d132769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74832 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24070 q ha hb
    | true =>
      simp only [d74832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74833 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74834 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74835 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74836 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74837 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24072 (p : Pattern) (ha : d74843 p = 1) (hb : d132769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74838 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24071 q ha hb
    | true =>
      simp only [d74838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74839 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74840 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74841 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74842 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74843 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24073 (p : Pattern) (ha : d74849 p = 1) (hb : d132769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74844 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24072 q ha hb
    | true =>
      simp only [d74844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74845 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74846 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74847 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74848 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74849 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24074 (p : Pattern) (ha : d53847 p = 1) (hb : d132769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53841 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d132766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53842 q = 1) (hb : d132768 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d132768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53842, d132768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d132768 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53843 q = 1) (hb : d132768 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53844 q = 1) (hb : d132768 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53845 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d132769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53845, d132769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53846 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53847 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h10 p ha hb
theorem andIntro24075 (p : Pattern) (ha : d53853 p = 1) (hb : d132769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24074 q ha hb
    | true =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24076 (p : Pattern) (ha : d53859 p = 1) (hb : d132769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24075 q ha hb
    | true =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24077 (p : Pattern) (ha : d53865 p = 1) (hb : d132769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24076 q ha hb
    | true =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d132769 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24078 (p : Pattern) (ha : d74849 p = 1) (hb : d104538 p = 1) : d74849 p = 1 := by
  have h0 (q : Pattern) (ha : d74849 q = 1) (hb : d104538 q = 1) : d74849 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro24079 (p : Pattern) (ha : d53865 p = 1) (hb : d104538 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d53865 q = 1) (hb : d104538 q = 1) : d53865 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro24080 (p : Pattern) (ha : d74831 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74827 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74828 q = 1) (hb : d132771 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74828, d132771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74828, d132771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d74829 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74829, d132772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74829, d132772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d74830 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74831 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro24081 (p : Pattern) (ha : d74837 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74832 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24080 q ha hb
    | true =>
      simp only [d74832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74833 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74834 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74835 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74836 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74837 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24082 (p : Pattern) (ha : d74843 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74838 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24081 q ha hb
    | true =>
      simp only [d74838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74839 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74840 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74841 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74842 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74843 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24083 (p : Pattern) (ha : d74849 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74844 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24082 q ha hb
    | true =>
      simp only [d74844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74845 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74846 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74847 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74848 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74849 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24084 (p : Pattern) (ha : d0 p = 1) (hb : d135136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135136 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro24085 (p : Pattern) (ha : d53847 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53843 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53844 q = 1) (hb : d132771 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d132771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53844, d132771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d132772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53845, d132772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53846 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53847 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro24086 (p : Pattern) (ha : d53853 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24085 q ha hb
    | true =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24087 (p : Pattern) (ha : d53859 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24086 q ha hb
    | true =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24088 (p : Pattern) (ha : d53865 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24087 q ha hb
    | true =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24089 (p : Pattern) (ha : d0 p = 1) (hb : d135427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135427 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro24090 (p : Pattern) (ha : d74831 p = 1) (hb : d135429 p = 1) : d109091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74826 q = 1) (hb : d85721 q = 1) : d109086 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74826, d109086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15898 q ha hb
    | true =>
      simp only [d74826, d109086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74827 q = 1) (hb : d85721 q = 1) : d109087 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74827, d109087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74827, d109087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d74828 q = 1) (hb : d135429 q = 1) : d109088 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74828, d135429, d109088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74828, d135429, d109088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d135429 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d74829 q = 1) (hb : d135429 q = 1) : d109089 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74829, d109089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74829, d109089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74830 q = 1) (hb : d135429 q = 1) : d109090 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, d109090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74830, d109090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d74831 q = 1) (hb : d135429 q = 1) : d109091 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, d109091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74831, d109091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro24091 (p : Pattern) (ha : d74837 p = 1) (hb : d135429 p = 1) : d109097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135429 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74832 q = 1) (hb : d135429 q = 1) : d109092 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, d109092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24090 q ha hb
    | true =>
      simp only [d74832, d109092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74833 q = 1) (hb : d135429 q = 1) : d109093 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, d109093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, d109093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74834 q = 1) (hb : d135429 q = 1) : d109094 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, d109094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, d109094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74835 q = 1) (hb : d135429 q = 1) : d109095 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74835, d109095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74835, d109095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74836 q = 1) (hb : d135429 q = 1) : d109096 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, d109096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74836, d109096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74837 q = 1) (hb : d135429 q = 1) : d109097 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, d109097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74837, d109097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24092 (p : Pattern) (ha : d74843 p = 1) (hb : d135429 p = 1) : d109103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135429 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74838 q = 1) (hb : d135429 q = 1) : d109098 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, d109098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24091 q ha hb
    | true =>
      simp only [d74838, d109098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74839 q = 1) (hb : d135429 q = 1) : d109099 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, d109099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, d109099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74840 q = 1) (hb : d135429 q = 1) : d109100 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, d109100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, d109100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74841 q = 1) (hb : d135429 q = 1) : d109101 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, d109101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, d109101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74842 q = 1) (hb : d135429 q = 1) : d109102 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, d109102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, d109102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74843 q = 1) (hb : d135429 q = 1) : d109103 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, d109103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74843, d109103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24093 (p : Pattern) (ha : d74849 p = 1) (hb : d135429 p = 1) : d109109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135429 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74844 q = 1) (hb : d135429 q = 1) : d109104 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, d109104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24092 q ha hb
    | true =>
      simp only [d74844, d109104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74845 q = 1) (hb : d135429 q = 1) : d109105 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, d109105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, d109105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74846 q = 1) (hb : d135429 q = 1) : d109106 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, d109106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, d109106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74847 q = 1) (hb : d135429 q = 1) : d109107 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, d109107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, d109107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74848 q = 1) (hb : d135429 q = 1) : d109108 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, d109108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, d109108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74849 q = 1) (hb : d135429 q = 1) : d109109 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, d109109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, d109109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24094 (p : Pattern) (ha : d53847 p = 1) (hb : d135429 p = 1) : d109304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d85721 q = 1) : d109299 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d109299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16167 q ha hb
    | true =>
      simp only [d53842, d109299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d85721 q = 1) : d109300 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d109300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d109300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53844 q = 1) (hb : d135429 q = 1) : d109301 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d135429, d109301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d135429, d109301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d135429 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53845 q = 1) (hb : d135429 q = 1) : d109302 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d109302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53845, d109302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53846 q = 1) (hb : d135429 q = 1) : d109303 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d109303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53846, d109303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d53847 q = 1) (hb : d135429 q = 1) : d109304 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d109304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53847, d109304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro24095 (p : Pattern) (ha : d53853 p = 1) (hb : d135429 p = 1) : d109310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135429 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d135429 q = 1) : d109305 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d109305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24094 q ha hb
    | true =>
      simp only [d53848, d109305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d135429 q = 1) : d109306 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d109306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d109306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d135429 q = 1) : d109307 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d109307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d109307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d135429 q = 1) : d109308 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d109308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d109308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d135429 q = 1) : d109309 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d109309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d109309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d135429 q = 1) : d109310 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d109310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d109310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24096 (p : Pattern) (ha : d53859 p = 1) (hb : d135429 p = 1) : d109316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135429 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d135429 q = 1) : d109311 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d109311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24095 q ha hb
    | true =>
      simp only [d53854, d109311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d135429 q = 1) : d109312 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d109312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d109312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d135429 q = 1) : d109313 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d109313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d109313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d135429 q = 1) : d109314 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d109314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d109314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d135429 q = 1) : d109315 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d109315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d109315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d135429 q = 1) : d109316 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d109316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d109316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24097 (p : Pattern) (ha : d53865 p = 1) (hb : d135429 p = 1) : d109322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135429 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d135429 q = 1) : d109317 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d109317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24096 q ha hb
    | true =>
      simp only [d53860, d109317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d135429 q = 1) : d109318 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d109318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d109318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d135429 q = 1) : d109319 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d109319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d109319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d135429 q = 1) : d109320 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d109320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d109320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d135429 q = 1) : d109321 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d109321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d109321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d135429 q = 1) : d109322 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d109322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d109322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24098 (p : Pattern) (ha : d36 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d31, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d34 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d35 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24099 (p : Pattern) (ha : d42 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24100 (p : Pattern) (ha : d48 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24101 (p : Pattern) (ha : d49 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24102 (p : Pattern) (ha : d55 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24103 (p : Pattern) (ha : d60 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24104 (p : Pattern) (ha : d77 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d72 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d73 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d76 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d77 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24105 (p : Pattern) (ha : d83 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24104 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24106 (p : Pattern) (ha : d89 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24105 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24107 (p : Pattern) (ha : d95 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24100 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24102 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24103 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24106 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24108 (p : Pattern) (ha : d104 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24109 (p : Pattern) (ha : d111 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24110 (p : Pattern) (ha : d213 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24111 (p : Pattern) (ha : d150 p = 1) (hb : d135431 p = 1) : d138044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145 q = 1) (hb : d135431 q = 1) : d138039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146 q = 1) (hb : d135431 q = 1) : d138040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147 q = 1) (hb : d135431 q = 1) : d138041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d31, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148 q = 1) (hb : d135431 q = 1) : d138042 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d34 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d149 q = 1) (hb : d135431 q = 1) : d138043 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d138043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d149, d138043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150 q = 1) (hb : d135431 q = 1) : d138044 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d138044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150, d138044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro24112 (p : Pattern) (ha : d203 p = 1) (hb : d135431 p = 1) : d138057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24111 q ha hb
    | true =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d155 q = 1) (hb : d135431 q = 1) : d138049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d203 q = 1) (hb : d135431 q = 1) : d138057 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d203, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24113 (p : Pattern) (ha : d4349 p = 1) (hb : d135431 p = 1) : d138068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24112 q ha hb
    | true =>
      simp only [d204, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
  have h2 (q : Pattern) (ha : d4340 q = 1) (hb : d135431 q = 1) : d138059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4340, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d135431 q = 1) : d138060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d138060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4341, d138060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d135431 q = 1) : d138061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d138061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d138061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d135431 q = 1) : d138062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d138062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d138062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d135431 q = 1) : d138068 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d138068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d138068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24114 (p : Pattern) (ha : d237 p = 1) (hb : d135431 p = 1) : d138079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d232 q = 1) (hb : d135431 q = 1) : d138074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d232, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d233 q = 1) (hb : d135431 q = 1) : d138075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234 q = 1) (hb : d135431 q = 1) : d138076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d72, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d235 q = 1) (hb : d135431 q = 1) : d138077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d235, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d75 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d236 q = 1) (hb : d135431 q = 1) : d138078 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d138078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d236, d138078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237 q = 1) (hb : d135431 q = 1) : d138079 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d138079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237, d138079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro24115 (p : Pattern) (ha : d243 p = 1) (hb : d135431 p = 1) : d138085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d135431 q = 1) : d138080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24114 q ha hb
    | true =>
      simp only [d238, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d135431 q = 1) : d138081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24104 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d240 q = 1) (hb : d135431 q = 1) : d138082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241 q = 1) (hb : d135431 q = 1) : d138083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d241, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d242 q = 1) (hb : d135431 q = 1) : d138084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d243 q = 1) (hb : d135431 q = 1) : d138085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24116 (p : Pattern) (ha : d4359 p = 1) (hb : d135431 p = 1) : d138091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d135431 q = 1) : d138086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24115 q ha hb
    | true =>
      simp only [d244, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24105 q ha hb
  have h2 (q : Pattern) (ha : d4355 q = 1) (hb : d135431 q = 1) : d138087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d138087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4355, d138087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24105 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d135431 q = 1) : d138088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d138088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4356, d138088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d135431 q = 1) : d138089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d138089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d138089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d135431 q = 1) : d138090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d138090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d138090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d135431 q = 1) : d138091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d138091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d138091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24117 (p : Pattern) (ha : d116 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24118 (p : Pattern) (ha : d123 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24119 (p : Pattern) (ha : d156 p = 1) (hb : d135431 p = 1) : d138050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24111 q ha hb
    | true =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d155 q = 1) (hb : d135431 q = 1) : d138049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d156 q = 1) (hb : d135431 q = 1) : d138050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24120 (p : Pattern) (ha : d51643 p = 1) (hb : d135431 p = 1) : d138056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24117 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24118 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d157 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24119 q ha hb
    | true =>
      simp only [d157, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
  have h9 (q : Pattern) (ha : d4335 q = 1) (hb : d135431 q = 1) : d138052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4335, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4336 q = 1) (hb : d135431 q = 1) : d138053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d138053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4336, d138053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51641 q = 1) (hb : d135431 q = 1) : d138054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d138054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51641, d138054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51642 q = 1) (hb : d135431 q = 1) : d138055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d138055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, d138055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51643 q = 1) (hb : d135431 q = 1) : d138056 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d138056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d138056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24121 (p : Pattern) (ha : d194 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24122 (p : Pattern) (ha : d199 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24123 (p : Pattern) (ha : d51646 p = 1) (hb : d135431 p = 1) : d138063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24117 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24118 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d157 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24119 q ha hb
    | true =>
      simp only [d157, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
  have h9 (q : Pattern) (ha : d4335 q = 1) (hb : d135431 q = 1) : d138052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4335, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4336 q = 1) (hb : d135431 q = 1) : d138053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d138053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4336, d138053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51641 q = 1) (hb : d135431 q = 1) : d138054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d138054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51641, d138054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51642 q = 1) (hb : d135431 q = 1) : d138055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d138055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, d138055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24121 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24122 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d204 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24112 q ha hb
    | true =>
      simp only [d204, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
  have h23 (q : Pattern) (ha : d4340 q = 1) (hb : d135431 q = 1) : d138059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4340, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d4341 q = 1) (hb : d135431 q = 1) : d138060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d138060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d4341, d138060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d51644 q = 1) (hb : d135431 q = 1) : d138061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d138061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51644, d138061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d51645 q = 1) (hb : d135431 q = 1) : d138062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d138062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51645, d138062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d51646 q = 1) (hb : d135431 q = 1) : d138063 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d138063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51646, d138063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro24124 (p : Pattern) (ha : d51652 p = 1) (hb : d135431 p = 1) : d138097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24108 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24108 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24109 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51647 q = 1) (hb : d135431 q = 1) : d138064 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d138064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24120 q ha hb
    | true =>
      simp only [d51647, d138064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24123 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24110 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d51648 q = 1) (hb : d135431 q = 1) : d138065 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d138065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51648, d138065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51649 q = 1) (hb : d135431 q = 1) : d138066 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d138066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51649, d138066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51650 q = 1) (hb : d135431 q = 1) : d138067 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d138067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51650, d138067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4350 q = 1) (hb : d135431 q = 1) : d138069 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d138069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d138069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24113 q ha hb
  have h12 (q : Pattern) (ha : d4351 q = 1) (hb : d135431 q = 1) : d138070 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d138070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4351, d138070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4352 q = 1) (hb : d135431 q = 1) : d138071 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d138071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4352, d138071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4353 q = 1) (hb : d135431 q = 1) : d138072 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d138072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4353, d138072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51651 q = 1) (hb : d135431 q = 1) : d138073 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d138073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51651, d138073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4360 q = 1) (hb : d135431 q = 1) : d138092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d138092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4360, d138092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24116 q ha hb
  have h17 (q : Pattern) (ha : d4361 q = 1) (hb : d135431 q = 1) : d138093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d138093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d4361, d138093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d4362 q = 1) (hb : d135431 q = 1) : d138094 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d138094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4362, d138094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4363 q = 1) (hb : d135431 q = 1) : d138095 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d138095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4363, d138095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4364 q = 1) (hb : d135431 q = 1) : d138096 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d138096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4364, d138096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51652 q = 1) (hb : d135431 q = 1) : d138097 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d138097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d51652, d138097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro24125 (p : Pattern) (ha : d284 p = 1) (hb : d135431 p = 1) : d138107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24119 q ha hb
    | true =>
      simp only [d157, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d135431 q = 1) : d138103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d135431 q = 1) : d138104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d135431 q = 1) : d138105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d135431 q = 1) : d138106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d284 q = 1) (hb : d135431 q = 1) : d138107 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d138107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d138107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24126 (p : Pattern) (ha : d291 p = 1) (hb : d135431 p = 1) : d138114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24119 q ha hb
    | true =>
      simp only [d157, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d135431 q = 1) : d138103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d135431 q = 1) : d138104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d135431 q = 1) : d138105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d135431 q = 1) : d138106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d204 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24112 q ha hb
    | true =>
      simp only [d204, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
  have h7 (q : Pattern) (ha : d287 q = 1) (hb : d135431 q = 1) : d138110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288 q = 1) (hb : d135431 q = 1) : d138111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d289 q = 1) (hb : d135431 q = 1) : d138112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290 q = 1) (hb : d135431 q = 1) : d138113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d291 q = 1) (hb : d135431 q = 1) : d138114 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d138114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d291, d138114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24127 (p : Pattern) (ha : d397 p = 1) (hb : d135431 p = 1) : d138165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24119 q ha hb
    | true =>
      simp only [d157, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d135431 q = 1) : d138103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d135431 q = 1) : d138104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d135431 q = 1) : d138105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d135431 q = 1) : d138106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24099 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d397 q = 1) (hb : d135431 q = 1) : d138165 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d138165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d397, d138165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24128 (p : Pattern) (ha : d406 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24129 (p : Pattern) (ha : d462 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24105 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24130 (p : Pattern) (ha : d296 p = 1) (hb : d135431 p = 1) : d138119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24111 q ha hb
    | true =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d295 q = 1) (hb : d135431 q = 1) : d138118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d296 q = 1) (hb : d135431 q = 1) : d138119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d138119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d138119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24131 (p : Pattern) (ha : d303 p = 1) (hb : d135431 p = 1) : d138126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24111 q ha hb
    | true =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d301 q = 1) (hb : d135431 q = 1) : d138124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302 q = 1) (hb : d135431 q = 1) : d138125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d302, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d303 q = 1) (hb : d135431 q = 1) : d138126 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d138126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d138126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24132 (p : Pattern) (ha : d330 p = 1) (hb : d135431 p = 1) : d138135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d324 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d325 q = 1) (hb : d135431 q = 1) : d138130 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d135431, d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d325, d135431, d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
  have h3 (q : Pattern) (ha : d326 q = 1) (hb : d135431 q = 1) : d138131 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d327 q = 1) (hb : d135431 q = 1) : d138132 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d144 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d145 q = 1) (hb : d135431 q = 1) : d138039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d145, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146 q = 1) (hb : d135431 q = 1) : d138040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147 q = 1) (hb : d135431 q = 1) : d138041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d328 q = 1) (hb : d135431 q = 1) : d138133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d328, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d31 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d31, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148 q = 1) (hb : d135431 q = 1) : d138042 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d329 q = 1) (hb : d135431 q = 1) : d138134 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d329, d138134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d329, d138134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d330 q = 1) (hb : d135431 q = 1) : d138135 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d330, d138135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d330, d138135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro24133 (p : Pattern) (ha : d336 p = 1) (hb : d135431 p = 1) : d138141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24132 q ha hb
    | true =>
      simp only [d331, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d332 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d332, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24111 q ha hb
    | true =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d333 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d334 q = 1) (hb : d135431 q = 1) : d138139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d334, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d335 q = 1) (hb : d135431 q = 1) : d138140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d335, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d336 q = 1) (hb : d135431 q = 1) : d138141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336, d138141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d336, d138141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24134 (p : Pattern) (ha : d4736 p = 1) (hb : d135431 p = 1) : d138050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24111 q ha hb
    | true =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d135431 q = 1) : d138049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d135431 q = 1) : d138050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24135 (p : Pattern) (ha : d74579 p = 1) (hb : d135431 p = 1) : d138147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d135431 q = 1) : d138120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d138120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24130 q ha hb
    | true =>
      simp only [d297, d138120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24117 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d135431 q = 1) : d138121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d138121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d138121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d135431 q = 1) : d138122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d138122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, d138122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d135431 q = 1) : d138123 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d138123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d138123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d135431 q = 1) : d138127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d138127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24131 q ha hb
    | true =>
      simp only [d304, d138127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24118 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d135431 q = 1) : d138128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d138128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d138128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d135431 q = 1) : d138129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d138129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, d138129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d337 q = 1) (hb : d135431 q = 1) : d138142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24133 q ha hb
    | true =>
      simp only [d337, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24119 q ha hb
  have h9 (q : Pattern) (ha : d4371 q = 1) (hb : d135431 q = 1) : d138143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d138143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4371, d138143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4737 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24134 q ha hb
    | true =>
      simp only [d4737, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5350 q = 1) (hb : d135431 q = 1) : d138052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5350, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74576 q = 1) (hb : d135431 q = 1) : d138144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74576, d138144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74576, d138144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74577 q = 1) (hb : d135431 q = 1) : d138145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74577, d138145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74577, d138145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74578 q = 1) (hb : d135431 q = 1) : d138146 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74578, d138146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74578, d138146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74579 q = 1) (hb : d135431 q = 1) : d138147 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74579, d138147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74579, d138147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24136 (p : Pattern) (ha : d376 p = 1) (hb : d135431 p = 1) : d138148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24111 q ha hb
    | true =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d295 q = 1) (hb : d135431 q = 1) : d138118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d376 q = 1) (hb : d135431 q = 1) : d138148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d138148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d376, d138148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24137 (p : Pattern) (ha : d381 p = 1) (hb : d135431 p = 1) : d138153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24111 q ha hb
    | true =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24098 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d301 q = 1) (hb : d135431 q = 1) : d138124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302 q = 1) (hb : d135431 q = 1) : d138125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d302, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d381 q = 1) (hb : d135431 q = 1) : d138153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d138153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d381, d138153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24138 (p : Pattern) (ha : d385 p = 1) (hb : d135431 p = 1) : d138157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24132 q ha hb
    | true =>
      simp only [d331, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d332 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d332, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24111 q ha hb
    | true =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d333 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d334 q = 1) (hb : d135431 q = 1) : d138139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d334, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d335 q = 1) (hb : d135431 q = 1) : d138140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d335, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d385 q = 1) (hb : d135431 q = 1) : d138157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d385, d138157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d385, d138157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24139 (p : Pattern) (ha : d5355 p = 1) (hb : d135431 p = 1) : d138057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24111 q ha hb
    | true =>
      simp only [d151, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d135431 q = 1) : d138049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d135431 q = 1) : d138057 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24140 (p : Pattern) (ha : d74583 p = 1) (hb : d135431 p = 1) : d138163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d135431 q = 1) : d138120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d138120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24130 q ha hb
    | true =>
      simp only [d297, d138120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24117 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d135431 q = 1) : d138121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d138121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d138121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d135431 q = 1) : d138122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d138122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, d138122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d135431 q = 1) : d138123 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d138123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d138123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d135431 q = 1) : d138127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d138127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24131 q ha hb
    | true =>
      simp only [d304, d138127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24118 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d135431 q = 1) : d138128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d138128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d138128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d135431 q = 1) : d138129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d138129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, d138129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d337 q = 1) (hb : d135431 q = 1) : d138142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24133 q ha hb
    | true =>
      simp only [d337, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24119 q ha hb
  have h9 (q : Pattern) (ha : d4371 q = 1) (hb : d135431 q = 1) : d138143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d138143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4371, d138143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4737 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24134 q ha hb
    | true =>
      simp only [d4737, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5350 q = 1) (hb : d135431 q = 1) : d138052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5350, d138052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74576 q = 1) (hb : d135431 q = 1) : d138144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74576, d138144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74576, d138144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74577 q = 1) (hb : d135431 q = 1) : d138145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74577, d138145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74577, d138145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74578 q = 1) (hb : d135431 q = 1) : d138146 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74578, d138146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74578, d138146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d377 q = 1) (hb : d135431 q = 1) : d138149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d138149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24136 q ha hb
    | true =>
      simp only [d377, d138149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24121 q ha hb
  have h16 (q : Pattern) (ha : d378 q = 1) (hb : d135431 q = 1) : d138150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d138150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d138150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d379 q = 1) (hb : d135431 q = 1) : d138151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d138151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d379, d138151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d380 q = 1) (hb : d135431 q = 1) : d138152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d138152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d138152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d382 q = 1) (hb : d135431 q = 1) : d138154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d138154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24137 q ha hb
    | true =>
      simp only [d382, d138154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24122 q ha hb
  have h20 (q : Pattern) (ha : d383 q = 1) (hb : d135431 q = 1) : d138155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d138155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d138155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d384 q = 1) (hb : d135431 q = 1) : d138156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d138156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d384, d138156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d386 q = 1) (hb : d135431 q = 1) : d138158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24138 q ha hb
    | true =>
      simp only [d386, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24112 q ha hb
  have h23 (q : Pattern) (ha : d4376 q = 1) (hb : d135431 q = 1) : d138159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d138159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4376, d138159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5356 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24139 q ha hb
    | true =>
      simp only [d5356, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5357 q = 1) (hb : d135431 q = 1) : d138059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5357, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74580 q = 1) (hb : d135431 q = 1) : d138160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74580, d138160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74580, d138160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74581 q = 1) (hb : d135431 q = 1) : d138161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74581, d138161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74581, d138161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74582 q = 1) (hb : d135431 q = 1) : d138162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74582, d138162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74582, d138162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74583 q = 1) (hb : d135431 q = 1) : d138163 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74583, d138163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74583, d138163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro24141 (p : Pattern) (ha : d74590 p = 1) (hb : d135431 p = 1) : d138172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d386 q = 1) (hb : d135431 q = 1) : d138158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24138 q ha hb
    | true =>
      simp only [d386, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24112 q ha hb
  have h2 (q : Pattern) (ha : d4376 q = 1) (hb : d135431 q = 1) : d138159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d138159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4376, d138159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24139 q ha hb
    | true =>
      simp only [d5356, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d135431 q = 1) : d138059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d138059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74580 q = 1) (hb : d135431 q = 1) : d138160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74580, d138160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74580, d138160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74588 q = 1) (hb : d135431 q = 1) : d138170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74588, d138170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74588, d138170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74589 q = 1) (hb : d135431 q = 1) : d138171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74589, d138171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74589, d138171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74590 q = 1) (hb : d135431 q = 1) : d138172 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74590, d138172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74590, d138172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24142 (p : Pattern) (ha : d423 p = 1) (hb : d135431 p = 1) : d138183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d417 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d418 q = 1) (hb : d135431 q = 1) : d138178 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d135431, d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d418, d135431, d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
  have h3 (q : Pattern) (ha : d419 q = 1) (hb : d135431 q = 1) : d138179 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d420 q = 1) (hb : d135431 q = 1) : d138180 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d231 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d232 q = 1) (hb : d135431 q = 1) : d138074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d232, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233 q = 1) (hb : d135431 q = 1) : d138075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234 q = 1) (hb : d135431 q = 1) : d138076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d421 q = 1) (hb : d135431 q = 1) : d138181 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d421, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d72 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d72, d135431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d73 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d235 q = 1) (hb : d135431 q = 1) : d138077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d235, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d422 q = 1) (hb : d135431 q = 1) : d138182 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d422, d138182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d422, d138182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d423 q = 1) (hb : d135431 q = 1) : d138183 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d423, d138183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d423, d138183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro24143 (p : Pattern) (ha : d429 p = 1) (hb : d135431 p = 1) : d138189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d424 q = 1) (hb : d135431 q = 1) : d138184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d424, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24142 q ha hb
    | true =>
      simp only [d424, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d425 q = 1) (hb : d135431 q = 1) : d138185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d425, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d425, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d135431 q = 1) : d138080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24114 q ha hb
    | true =>
      simp only [d238, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d135431 q = 1) : d138081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d426 q = 1) (hb : d135431 q = 1) : d138186 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d426, d138186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d426, d138186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d427 q = 1) (hb : d135431 q = 1) : d138187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d427, d138187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d427, d138187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d428 q = 1) (hb : d135431 q = 1) : d138188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d428, d138188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d428, d138188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d429 q = 1) (hb : d135431 q = 1) : d138189 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d429, d138189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d429, d138189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24144 (p : Pattern) (ha : d5377 p = 1) (hb : d135431 p = 1) : d138085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d135431 q = 1) : d138080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24114 q ha hb
    | true =>
      simp only [d238, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d135431 q = 1) : d138081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d135431 q = 1) : d138082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d135431 q = 1) : d138083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d135431 q = 1) : d138084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d135431 q = 1) : d138085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24145 (p : Pattern) (ha : d74599 p = 1) (hb : d135431 p = 1) : d138195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d430 q = 1) (hb : d135431 q = 1) : d138190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d430, d138190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24143 q ha hb
    | true =>
      simp only [d430, d138190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24115 q ha hb
  have h2 (q : Pattern) (ha : d4391 q = 1) (hb : d135431 q = 1) : d138191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d138191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4391, d138191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d135431 q = 1) : d138086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24144 q ha hb
    | true =>
      simp only [d5378, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d135431 q = 1) : d138087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d138087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d138087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74596 q = 1) (hb : d135431 q = 1) : d138192 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74596, d138192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74596, d138192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74597 q = 1) (hb : d135431 q = 1) : d138193 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74597, d138193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74597, d138193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74598 q = 1) (hb : d135431 q = 1) : d138194 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74598, d138194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74598, d138194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74599 q = 1) (hb : d135431 q = 1) : d138195 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74599, d138195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74599, d138195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24146 (p : Pattern) (ha : d74605 p = 1) (hb : d135431 p = 1) : d138201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d135431 q = 1) : d138108 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d138108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d138108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24125 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d135431 q = 1) : d138109 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d138109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d138109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d135431 q = 1) : d138115 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d138115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24125 q ha hb
    | true =>
      simp only [d292, d138115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24126 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d135431 q = 1) : d138116 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d138116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d138116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d135431 q = 1) : d138117 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d138117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d138117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74584 q = 1) (hb : d135431 q = 1) : d138164 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74584, d138164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24135 q ha hb
    | true =>
      simp only [d74584, d138164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24140 q ha hb
  have h7 (q : Pattern) (ha : d398 q = 1) (hb : d135431 q = 1) : d138166 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d138166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24127 q ha hb
    | true =>
      simp only [d398, d138166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24109 q ha hb
  have h8 (q : Pattern) (ha : d74585 q = 1) (hb : d135431 q = 1) : d138167 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74585, d138167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74585, d138167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74586 q = 1) (hb : d135431 q = 1) : d138168 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74586, d138168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74586, d138168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74587 q = 1) (hb : d135431 q = 1) : d138169 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74587, d138169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74587, d138169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74591 q = 1) (hb : d135431 q = 1) : d138173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74591, d138173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74591, d138173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24141 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24128 q ha hb
  have h13 (q : Pattern) (ha : d74592 q = 1) (hb : d135431 q = 1) : d138174 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74592, d138174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74592, d138174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74593 q = 1) (hb : d135431 q = 1) : d138175 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74593, d138175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74593, d138175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74594 q = 1) (hb : d135431 q = 1) : d138176 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74594, d138176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74594, d138176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74595 q = 1) (hb : d135431 q = 1) : d138177 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74595, d138177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74595, d138177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74600 q = 1) (hb : d135431 q = 1) : d138196 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74600, d138196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74600, d138196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24145 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24129 q ha hb
  have h19 (q : Pattern) (ha : d74601 q = 1) (hb : d135431 q = 1) : d138197 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74601, d138197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74601, d138197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74602 q = 1) (hb : d135431 q = 1) : d138198 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74602, d138198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74602, d138198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74603 q = 1) (hb : d135431 q = 1) : d138199 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74603, d138199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74603, d138199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74604 q = 1) (hb : d135431 q = 1) : d138200 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74604, d138200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74604, d138200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74605 q = 1) (hb : d135431 q = 1) : d138201 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74605, d138201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74605, d138201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24147 (p : Pattern) (ha : d74611 p = 1) (hb : d135431 p = 1) : d138207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24107 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51653 q = 1) (hb : d135431 q = 1) : d138098 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d138098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51653, d138098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24124 q ha hb
  have h6 (q : Pattern) (ha : d51654 q = 1) (hb : d135431 q = 1) : d138099 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d138099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51654, d138099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51655 q = 1) (hb : d135431 q = 1) : d138100 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d138100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51655, d138100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51656 q = 1) (hb : d135431 q = 1) : d138101 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d138101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51656, d138101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51657 q = 1) (hb : d135431 q = 1) : d138102 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d138102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51657, d138102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74606 q = 1) (hb : d135431 q = 1) : d138202 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74606, d138202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74606, d138202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24146 q ha hb
  have h11 (q : Pattern) (ha : d74607 q = 1) (hb : d135431 q = 1) : d138203 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74607, d138203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74607, d138203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74608 q = 1) (hb : d135431 q = 1) : d138204 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74608, d138204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74608, d138204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74609 q = 1) (hb : d135431 q = 1) : d138205 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74609, d138205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74609, d138205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74610 q = 1) (hb : d135431 q = 1) : d138206 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74610, d138206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74610, d138206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74611 q = 1) (hb : d135431 q = 1) : d138207 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74611, d138207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74611, d138207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24148 (p : Pattern) (ha : d477 p = 1) (hb : d135431 p = 1) : d138135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d324 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d325 q = 1) (hb : d135431 q = 1) : d138130 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d135431, d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d325, d135431, d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
  have h3 (q : Pattern) (ha : d326 q = 1) (hb : d135431 q = 1) : d138131 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d327 q = 1) (hb : d135431 q = 1) : d138132 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d144 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d145 q = 1) (hb : d135431 q = 1) : d138039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d145, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146 q = 1) (hb : d135431 q = 1) : d138040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147 q = 1) (hb : d135431 q = 1) : d138041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d328 q = 1) (hb : d135431 q = 1) : d138133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d328, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d475 q = 1) (hb : d135431 q = 1) : d138042 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d475, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d476 q = 1) (hb : d135431 q = 1) : d138134 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d476, d138134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d476, d138134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d477 q = 1) (hb : d135431 q = 1) : d138135 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d477, d138135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d477, d138135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro24149 (p : Pattern) (ha : d481 p = 1) (hb : d135431 p = 1) : d138044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d145 q = 1) (hb : d135431 q = 1) : d138039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d145, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146 q = 1) (hb : d135431 q = 1) : d138040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147 q = 1) (hb : d135431 q = 1) : d138041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d475 q = 1) (hb : d135431 q = 1) : d138042 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d475, d138042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d480 q = 1) (hb : d135431 q = 1) : d138043 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d138043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d480, d138043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d481 q = 1) (hb : d135431 q = 1) : d138044 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d138044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d481, d138044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24150 (p : Pattern) (ha : d487 p = 1) (hb : d135431 p = 1) : d138141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24148 q ha hb
    | true =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24149 q ha hb
    | true =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d485 q = 1) (hb : d135431 q = 1) : d138139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d485, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d486 q = 1) (hb : d135431 q = 1) : d138140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d486, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d486, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d487 q = 1) (hb : d135431 q = 1) : d138141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d487, d138141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d487, d138141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24151 (p : Pattern) (ha : d491 p = 1) (hb : d135431 p = 1) : d138050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24149 q ha hb
    | true =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d135431 q = 1) : d138049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d135431 q = 1) : d138050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d138050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24152 (p : Pattern) (ha : d497 p = 1) (hb : d135431 p = 1) : d138212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d492 q = 1) (hb : d135431 q = 1) : d138142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24150 q ha hb
    | true =>
      simp only [d492, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24151 q ha hb
  have h2 (q : Pattern) (ha : d493 q = 1) (hb : d135431 q = 1) : d138208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d135431 q = 1) : d138209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d494, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d135431 q = 1) : d138210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d135431 q = 1) : d138211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d497 q = 1) (hb : d135431 q = 1) : d138212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, d138212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, d138212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24153 (p : Pattern) (ha : d500 p = 1) (hb : d135431 p = 1) : d138157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24148 q ha hb
    | true =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24149 q ha hb
    | true =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d485 q = 1) (hb : d135431 q = 1) : d138139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d485, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d486 q = 1) (hb : d135431 q = 1) : d138140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d486, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d486, d138140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d500 q = 1) (hb : d135431 q = 1) : d138157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d500, d138157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d500, d138157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24154 (p : Pattern) (ha : d501 p = 1) (hb : d135431 p = 1) : d138057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24149 q ha hb
    | true =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d135431 q = 1) : d138049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d138049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d135431 q = 1) : d138057 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d138057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24155 (p : Pattern) (ha : d507 p = 1) (hb : d135431 p = 1) : d138219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d492 q = 1) (hb : d135431 q = 1) : d138142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24150 q ha hb
    | true =>
      simp only [d492, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24151 q ha hb
  have h2 (q : Pattern) (ha : d493 q = 1) (hb : d135431 q = 1) : d138208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d135431 q = 1) : d138209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d494, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d135431 q = 1) : d138210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d135431 q = 1) : d138211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d502 q = 1) (hb : d135431 q = 1) : d138158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24153 q ha hb
    | true =>
      simp only [d502, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24154 q ha hb
  have h7 (q : Pattern) (ha : d503 q = 1) (hb : d135431 q = 1) : d138215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d504 q = 1) (hb : d135431 q = 1) : d138216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d504, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d505 q = 1) (hb : d135431 q = 1) : d138217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d506 q = 1) (hb : d135431 q = 1) : d138218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d507 q = 1) (hb : d135431 q = 1) : d138219 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d507, d138219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d507, d138219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24156 (p : Pattern) (ha : d638 p = 1) (hb : d135431 p = 1) : d138279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d492 q = 1) (hb : d135431 q = 1) : d138142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24150 q ha hb
    | true =>
      simp only [d492, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24151 q ha hb
  have h2 (q : Pattern) (ha : d493 q = 1) (hb : d135431 q = 1) : d138208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d135431 q = 1) : d138209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d494, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d135431 q = 1) : d138210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d135431 q = 1) : d138211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24151 q ha hb
    | true =>
      simp only [d633, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d135431 q = 1) : d138103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d135431 q = 1) : d138104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d135431 q = 1) : d138105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d135431 q = 1) : d138106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d638 q = 1) (hb : d135431 q = 1) : d138279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d638, d138279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d638, d138279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24157 (p : Pattern) (ha : d644 p = 1) (hb : d135431 p = 1) : d138114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d135431 q = 1) : d138051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24151 q ha hb
    | true =>
      simp only [d633, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d135431 q = 1) : d138103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d135431 q = 1) : d138104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d135431 q = 1) : d138105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d135431 q = 1) : d138106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24154 q ha hb
    | true =>
      simp only [d639, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d135431 q = 1) : d138110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d135431 q = 1) : d138111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d135431 q = 1) : d138112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d135431 q = 1) : d138113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d135431 q = 1) : d138114 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d138114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d138114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24158 (p : Pattern) (ha : d653 p = 1) (hb : d135431 p = 1) : d138288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24154 q ha hb
    | true =>
      simp only [d639, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d135431 q = 1) : d138110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d135431 q = 1) : d138111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d135431 q = 1) : d138112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d135431 q = 1) : d138113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d135431 q = 1) : d138288 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d138288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d138288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24159 (p : Pattern) (ha : d683 p = 1) (hb : d135431 p = 1) : d138079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d231 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d232 q = 1) (hb : d135431 q = 1) : d138074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d232, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d233 q = 1) (hb : d135431 q = 1) : d138075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d234 q = 1) (hb : d135431 q = 1) : d138076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d673 q = 1) (hb : d135431 q = 1) : d138077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d673, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d682 q = 1) (hb : d135431 q = 1) : d138078 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d138078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d682, d138078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d683 q = 1) (hb : d135431 q = 1) : d138079 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d138079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d683, d138079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24160 (p : Pattern) (ha : d730 p = 1) (hb : d135431 p = 1) : d138085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d135431 q = 1) : d138080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24159 q ha hb
    | true =>
      simp only [d684, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d135431 q = 1) : d138081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d135431 q = 1) : d138082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d138082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d135431 q = 1) : d138083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d138083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d135431 q = 1) : d138084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d138084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d135431 q = 1) : d138085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d138085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24161 (p : Pattern) (ha : d736 p = 1) (hb : d135431 p = 1) : d138323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d135431 q = 1) : d138086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24160 q ha hb
    | true =>
      simp only [d731, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d135431 q = 1) : d138319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d138319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d138319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d135431 q = 1) : d138320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d138320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d138320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d135431 q = 1) : d138321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d138321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d138321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d135431 q = 1) : d138322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d138322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d138322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d135431 q = 1) : d138323 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d138323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d138323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24162 (p : Pattern) (ha : d512 p = 1) (hb : d135431 p = 1) : d138224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24148 q ha hb
    | true =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24149 q ha hb
    | true =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d485 q = 1) (hb : d135431 q = 1) : d138139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d485, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d511 q = 1) (hb : d135431 q = 1) : d138223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, d138223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d511, d138223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d512 q = 1) (hb : d135431 q = 1) : d138224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d512, d138224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d512, d138224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24163 (p : Pattern) (ha : d514 p = 1) (hb : d135431 p = 1) : d138119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24149 q ha hb
    | true =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d135431 q = 1) : d138118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d135431 q = 1) : d138119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d138119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d138119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24164 (p : Pattern) (ha : d521 p = 1) (hb : d135431 p = 1) : d138231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24148 q ha hb
    | true =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24149 q ha hb
    | true =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d519 q = 1) (hb : d135431 q = 1) : d138229 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d138229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d519, d138229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d520 q = 1) (hb : d135431 q = 1) : d138230 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, d138230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d520, d138230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d521 q = 1) (hb : d135431 q = 1) : d138231 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d521, d138231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d521, d138231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24165 (p : Pattern) (ha : d524 p = 1) (hb : d135431 p = 1) : d138126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24149 q ha hb
    | true =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d135431 q = 1) : d138124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d135431 q = 1) : d138125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d135431 q = 1) : d138126 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d138126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d138126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24166 (p : Pattern) (ha : d554 p = 1) (hb : d135431 p = 1) : d138240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d548 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d549 q = 1) (hb : d135431 q = 1) : d138235 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d549, d135431, d138235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d549, d135431, d138235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12463 q ha hb
  have h3 (q : Pattern) (ha : d550 q = 1) (hb : d135431 q = 1) : d138236 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d550, d138236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d550, d138236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d551 q = 1) (hb : d135431 q = 1) : d138237 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d551, d138237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d551, d138237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d324 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d325 q = 1) (hb : d135431 q = 1) : d138130 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d135431, d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d325, d135431, d138130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
  have h7 (q : Pattern) (ha : d326 q = 1) (hb : d135431 q = 1) : d138131 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d138131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d327 q = 1) (hb : d135431 q = 1) : d138132 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d138132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d552 q = 1) (hb : d135431 q = 1) : d138238 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d552, d138238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d552, d138238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d144 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d94753 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d145 q = 1) (hb : d135431 q = 1) : d138039 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d145, d135431, d138039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146 q = 1) (hb : d135431 q = 1) : d138040 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d138040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147 q = 1) (hb : d135431 q = 1) : d138041 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d138041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d328 q = 1) (hb : d135431 q = 1) : d138133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d328, d138133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d553 q = 1) (hb : d135431 q = 1) : d138239 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d553, d138239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d553, d138239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d554 q = 1) (hb : d135431 q = 1) : d138240 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d554, d138240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d554, d138240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro24167 (p : Pattern) (ha : d560 p = 1) (hb : d135431 p = 1) : d138246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d555 q = 1) (hb : d135431 q = 1) : d138241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d138241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24166 q ha hb
    | true =>
      simp only [d555, d138241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d556 q = 1) (hb : d135431 q = 1) : d138242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d138242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d556, d138242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d478 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24148 q ha hb
    | true =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d479 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d557 q = 1) (hb : d135431 q = 1) : d138243 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d557, d138243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d557, d138243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d558 q = 1) (hb : d135431 q = 1) : d138244 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d558, d138244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d558, d138244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d559 q = 1) (hb : d135431 q = 1) : d138245 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d559, d138245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d559, d138245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d560 q = 1) (hb : d135431 q = 1) : d138246 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d560, d138246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d560, d138246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24168 (p : Pattern) (ha : d5399 p = 1) (hb : d135431 p = 1) : d138252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24148 q ha hb
    | true =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5396 q = 1) (hb : d135431 q = 1) : d138249 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d138249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5396, d138249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5397 q = 1) (hb : d135431 q = 1) : d138250 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d138250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5397, d138250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5398 q = 1) (hb : d135431 q = 1) : d138251 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d138251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5398, d138251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5399 q = 1) (hb : d135431 q = 1) : d138252 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5399, d138252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5399, d138252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24169 (p : Pattern) (ha : d74615 p = 1) (hb : d135431 p = 1) : d138258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d515 q = 1) (hb : d135431 q = 1) : d138225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d138225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24162 q ha hb
    | true =>
      simp only [d515, d138225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24163 q ha hb
  have h2 (q : Pattern) (ha : d516 q = 1) (hb : d135431 q = 1) : d138226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d138226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d138226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d517 q = 1) (hb : d135431 q = 1) : d138227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d138227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d517, d138227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d518 q = 1) (hb : d135431 q = 1) : d138228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d138228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d138228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d525 q = 1) (hb : d135431 q = 1) : d138232 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d138232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24164 q ha hb
    | true =>
      simp only [d525, d138232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24165 q ha hb
  have h6 (q : Pattern) (ha : d526 q = 1) (hb : d135431 q = 1) : d138233 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d138233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d138233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d527 q = 1) (hb : d135431 q = 1) : d138234 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d138234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d527, d138234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d561 q = 1) (hb : d135431 q = 1) : d138247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d138247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24167 q ha hb
    | true =>
      simp only [d561, d138247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24150 q ha hb
  have h9 (q : Pattern) (ha : d4408 q = 1) (hb : d135431 q = 1) : d138248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d138248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4408, d138248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5400 q = 1) (hb : d135431 q = 1) : d138253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d138253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24168 q ha hb
    | true =>
      simp only [d5400, d138253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5401 q = 1) (hb : d135431 q = 1) : d138254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d138254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5401, d138254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74612 q = 1) (hb : d135431 q = 1) : d138255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74612, d138255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74612, d138255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74613 q = 1) (hb : d135431 q = 1) : d138256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74613, d138256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74613, d138256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74614 q = 1) (hb : d135431 q = 1) : d138257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74614, d138257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74614, d138257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74615 q = 1) (hb : d135431 q = 1) : d138258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74615, d138258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74615, d138258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24170 (p : Pattern) (ha : d609 p = 1) (hb : d135431 p = 1) : d138259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24148 q ha hb
    | true =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24149 q ha hb
    | true =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d485 q = 1) (hb : d135431 q = 1) : d138139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d485, d138139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d511 q = 1) (hb : d135431 q = 1) : d138223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, d138223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d511, d138223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d609 q = 1) (hb : d135431 q = 1) : d138259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d609, d138259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d609, d138259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24171 (p : Pattern) (ha : d610 p = 1) (hb : d135431 p = 1) : d138148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24149 q ha hb
    | true =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d135431 q = 1) : d138048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d138048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d135431 q = 1) : d138118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d138118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d135431 q = 1) : d138148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d138148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d138148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24172 (p : Pattern) (ha : d615 p = 1) (hb : d135431 p = 1) : d138264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24148 q ha hb
    | true =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24149 q ha hb
    | true =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d135431 q = 1) : d138138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d138138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d519 q = 1) (hb : d135431 q = 1) : d138229 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d138229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d519, d138229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d520 q = 1) (hb : d135431 q = 1) : d138230 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, d138230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d520, d138230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d615 q = 1) (hb : d135431 q = 1) : d138264 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d615, d138264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d615, d138264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24173 (p : Pattern) (ha : d616 p = 1) (hb : d135431 p = 1) : d138153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d135431 q = 1) : d138045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24149 q ha hb
    | true =>
      simp only [d482, d138045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d135431 q = 1) : d138046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d138046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d135431 q = 1) : d138047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d138047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d135431 q = 1) : d138124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d138124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d135431 q = 1) : d138125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d138125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d135431 q = 1) : d138153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d138153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d138153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24174 (p : Pattern) (ha : d620 p = 1) (hb : d135431 p = 1) : d138268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d555 q = 1) (hb : d135431 q = 1) : d138241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d138241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24166 q ha hb
    | true =>
      simp only [d555, d138241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d556 q = 1) (hb : d135431 q = 1) : d138242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d138242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d556, d138242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d478 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24148 q ha hb
    | true =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d479 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d557 q = 1) (hb : d135431 q = 1) : d138243 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d557, d138243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d557, d138243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d558 q = 1) (hb : d135431 q = 1) : d138244 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d558, d138244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d558, d138244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d559 q = 1) (hb : d135431 q = 1) : d138245 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d559, d138245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d559, d138245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d620 q = 1) (hb : d135431 q = 1) : d138268 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d620, d138268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d620, d138268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24175 (p : Pattern) (ha : d5406 p = 1) (hb : d135431 p = 1) : d138271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d135431 q = 1) : d138136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24148 q ha hb
    | true =>
      simp only [d478, d138136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d135431 q = 1) : d138137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d138137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5396 q = 1) (hb : d135431 q = 1) : d138249 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d138249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5396, d138249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5397 q = 1) (hb : d135431 q = 1) : d138250 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d138250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5397, d138250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5398 q = 1) (hb : d135431 q = 1) : d138251 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d138251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5398, d138251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5406 q = 1) (hb : d135431 q = 1) : d138271 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5406, d138271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5406, d138271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24176 (p : Pattern) (ha : d74619 p = 1) (hb : d135431 p = 1) : d138277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d515 q = 1) (hb : d135431 q = 1) : d138225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d138225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24162 q ha hb
    | true =>
      simp only [d515, d138225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24163 q ha hb
  have h2 (q : Pattern) (ha : d516 q = 1) (hb : d135431 q = 1) : d138226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d138226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d138226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d517 q = 1) (hb : d135431 q = 1) : d138227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d138227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d517, d138227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d518 q = 1) (hb : d135431 q = 1) : d138228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d138228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d138228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d525 q = 1) (hb : d135431 q = 1) : d138232 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d138232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24164 q ha hb
    | true =>
      simp only [d525, d138232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24165 q ha hb
  have h6 (q : Pattern) (ha : d526 q = 1) (hb : d135431 q = 1) : d138233 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d138233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d138233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d527 q = 1) (hb : d135431 q = 1) : d138234 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d138234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d527, d138234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d561 q = 1) (hb : d135431 q = 1) : d138247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d138247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24167 q ha hb
    | true =>
      simp only [d561, d138247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24150 q ha hb
  have h9 (q : Pattern) (ha : d4408 q = 1) (hb : d135431 q = 1) : d138248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d138248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4408, d138248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5400 q = 1) (hb : d135431 q = 1) : d138253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d138253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24168 q ha hb
    | true =>
      simp only [d5400, d138253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5401 q = 1) (hb : d135431 q = 1) : d138254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d138254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5401, d138254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74612 q = 1) (hb : d135431 q = 1) : d138255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74612, d138255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74612, d138255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74613 q = 1) (hb : d135431 q = 1) : d138256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74613, d138256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74613, d138256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74614 q = 1) (hb : d135431 q = 1) : d138257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74614, d138257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74614, d138257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d611 q = 1) (hb : d135431 q = 1) : d138260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d611, d138260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24170 q ha hb
    | true =>
      simp only [d611, d138260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24171 q ha hb
  have h16 (q : Pattern) (ha : d612 q = 1) (hb : d135431 q = 1) : d138261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, d138261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d612, d138261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d613 q = 1) (hb : d135431 q = 1) : d138262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, d138262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d613, d138262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d614 q = 1) (hb : d135431 q = 1) : d138263 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, d138263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d614, d138263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d617 q = 1) (hb : d135431 q = 1) : d138265 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d617, d138265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24172 q ha hb
    | true =>
      simp only [d617, d138265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24173 q ha hb
  have h20 (q : Pattern) (ha : d618 q = 1) (hb : d135431 q = 1) : d138266 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, d138266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d618, d138266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d619 q = 1) (hb : d135431 q = 1) : d138267 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d138267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d619, d138267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d621 q = 1) (hb : d135431 q = 1) : d138269 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d138269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24174 q ha hb
    | true =>
      simp only [d621, d138269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24153 q ha hb
  have h23 (q : Pattern) (ha : d4413 q = 1) (hb : d135431 q = 1) : d138270 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d138270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4413, d138270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5407 q = 1) (hb : d135431 q = 1) : d138272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d138272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24175 q ha hb
    | true =>
      simp only [d5407, d138272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5408 q = 1) (hb : d135431 q = 1) : d138273 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d138273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5408, d138273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74616 q = 1) (hb : d135431 q = 1) : d138274 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74616, d138274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74616, d138274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74617 q = 1) (hb : d135431 q = 1) : d138275 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74617, d138275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74617, d138275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74618 q = 1) (hb : d135431 q = 1) : d138276 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74618, d138276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74618, d138276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74619 q = 1) (hb : d135431 q = 1) : d138277 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74619, d138277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74619, d138277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro24177 (p : Pattern) (ha : d74626 p = 1) (hb : d135431 p = 1) : d138286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d621 q = 1) (hb : d135431 q = 1) : d138269 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d138269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24174 q ha hb
    | true =>
      simp only [d621, d138269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24153 q ha hb
  have h2 (q : Pattern) (ha : d4413 q = 1) (hb : d135431 q = 1) : d138270 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d138270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4413, d138270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5407 q = 1) (hb : d135431 q = 1) : d138272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d138272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24175 q ha hb
    | true =>
      simp only [d5407, d138272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5408 q = 1) (hb : d135431 q = 1) : d138273 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d138273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5408, d138273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74616 q = 1) (hb : d135431 q = 1) : d138274 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74616, d138274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74616, d138274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74624 q = 1) (hb : d135431 q = 1) : d138284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74624, d138284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74624, d138284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74625 q = 1) (hb : d135431 q = 1) : d138285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74625, d138285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74625, d138285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74626 q = 1) (hb : d135431 q = 1) : d138286 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74626, d138286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74626, d138286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24178 (p : Pattern) (ha : d670 p = 1) (hb : d135431 p = 1) : d138299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d664 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d665 q = 1) (hb : d135431 q = 1) : d138294 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, d135431, d138294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d665, d135431, d138294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12479 q ha hb
  have h3 (q : Pattern) (ha : d666 q = 1) (hb : d135431 q = 1) : d138295 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, d138295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d666, d138295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d667 q = 1) (hb : d135431 q = 1) : d138296 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, d138296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d667, d138296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d417 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d418 q = 1) (hb : d135431 q = 1) : d138178 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d135431, d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d418, d135431, d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
  have h7 (q : Pattern) (ha : d419 q = 1) (hb : d135431 q = 1) : d138179 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d420 q = 1) (hb : d135431 q = 1) : d138180 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d668 q = 1) (hb : d135431 q = 1) : d138297 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d668, d138297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d668, d138297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d231 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d232 q = 1) (hb : d135431 q = 1) : d138074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d232, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d233 q = 1) (hb : d135431 q = 1) : d138075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234 q = 1) (hb : d135431 q = 1) : d138076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d421 q = 1) (hb : d135431 q = 1) : d138181 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d421, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d669 q = 1) (hb : d135431 q = 1) : d138298 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d669, d138298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d669, d138298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d670 q = 1) (hb : d135431 q = 1) : d138299 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d670, d138299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d670, d138299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro24179 (p : Pattern) (ha : d675 p = 1) (hb : d135431 p = 1) : d138183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d417 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d418 q = 1) (hb : d135431 q = 1) : d138178 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d135431, d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d418, d135431, d138178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
  have h3 (q : Pattern) (ha : d419 q = 1) (hb : d135431 q = 1) : d138179 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d138179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d420 q = 1) (hb : d135431 q = 1) : d138180 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d138180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d231 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d71 q = 1) (hb : d94753 q = 1) : d71 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d232 q = 1) (hb : d135431 q = 1) : d138074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d232, d135431, d138074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233 q = 1) (hb : d135431 q = 1) : d138075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d138075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234 q = 1) (hb : d135431 q = 1) : d138076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d138076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d421 q = 1) (hb : d135431 q = 1) : d138181 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d421, d138181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d673 q = 1) (hb : d135431 q = 1) : d138077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d673, d138077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d674 q = 1) (hb : d135431 q = 1) : d138182 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d674, d138182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d674, d138182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d675 q = 1) (hb : d135431 q = 1) : d138183 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d675, d138183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d675, d138183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro24180 (p : Pattern) (ha : d681 p = 1) (hb : d135431 p = 1) : d138305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d671 q = 1) (hb : d135431 q = 1) : d138300 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d671, d138300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24178 q ha hb
    | true =>
      simp only [d671, d138300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d672 q = 1) (hb : d135431 q = 1) : d138301 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d672, d138301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d672, d138301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d676 q = 1) (hb : d135431 q = 1) : d138184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24179 q ha hb
    | true =>
      simp only [d676, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d677 q = 1) (hb : d135431 q = 1) : d138185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d678 q = 1) (hb : d135431 q = 1) : d138302 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d678, d138302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d678, d138302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d679 q = 1) (hb : d135431 q = 1) : d138303 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d679, d138303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d679, d138303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d680 q = 1) (hb : d135431 q = 1) : d138304 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d680, d138304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d680, d138304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d681 q = 1) (hb : d135431 q = 1) : d138305 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d681, d138305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d681, d138305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24181 (p : Pattern) (ha : d689 p = 1) (hb : d135431 p = 1) : d138189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d135431 q = 1) : d138184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24179 q ha hb
    | true =>
      simp only [d676, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d135431 q = 1) : d138185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d135431 q = 1) : d138080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24159 q ha hb
    | true =>
      simp only [d684, d138080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d135431 q = 1) : d138081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d138081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d686 q = 1) (hb : d135431 q = 1) : d138186 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d686, d138186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d686, d138186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d687 q = 1) (hb : d135431 q = 1) : d138187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d687, d138187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d687, d138187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d688 q = 1) (hb : d135431 q = 1) : d138188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d688, d138188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d688, d138188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d689 q = 1) (hb : d135431 q = 1) : d138189 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d689, d138189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d689, d138189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24182 (p : Pattern) (ha : d5428 p = 1) (hb : d135431 p = 1) : d138311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d135431 q = 1) : d138184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24179 q ha hb
    | true =>
      simp only [d676, d138184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d135431 q = 1) : d138185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d138185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5425 q = 1) (hb : d135431 q = 1) : d138308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5425, d138308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5425, d138308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5426 q = 1) (hb : d135431 q = 1) : d138309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5426, d138309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5426, d138309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5427 q = 1) (hb : d135431 q = 1) : d138310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5427, d138310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5427, d138310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5428 q = 1) (hb : d135431 q = 1) : d138311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5428, d138311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5428, d138311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24183 (p : Pattern) (ha : d74635 p = 1) (hb : d135431 p = 1) : d138317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d690 q = 1) (hb : d135431 q = 1) : d138306 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d690, d138306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24180 q ha hb
    | true =>
      simp only [d690, d138306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24181 q ha hb
  have h2 (q : Pattern) (ha : d4428 q = 1) (hb : d135431 q = 1) : d138307 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4428, d138307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4428, d138307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5429 q = 1) (hb : d135431 q = 1) : d138312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5429, d138312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24182 q ha hb
    | true =>
      simp only [d5429, d138312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5430 q = 1) (hb : d135431 q = 1) : d138313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5430, d138313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5430, d138313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74632 q = 1) (hb : d135431 q = 1) : d138314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74632, d138314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74632, d138314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74633 q = 1) (hb : d135431 q = 1) : d138315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74633, d138315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74633, d138315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74634 q = 1) (hb : d135431 q = 1) : d138316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74634, d138316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74634, d138316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74635 q = 1) (hb : d135431 q = 1) : d138317 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74635, d138317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74635, d138317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24184 (p : Pattern) (ha : d74641 p = 1) (hb : d135431 p = 1) : d138329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d135431 q = 1) : d138213 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d138213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d138213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24152 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d135431 q = 1) : d138214 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d138214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d138214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d135431 q = 1) : d138220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d138220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24152 q ha hb
    | true =>
      simp only [d508, d138220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24155 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d135431 q = 1) : d138221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d138221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d138221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d135431 q = 1) : d138222 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d138222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d138222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74620 q = 1) (hb : d135431 q = 1) : d138278 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74620, d138278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24169 q ha hb
    | true =>
      simp only [d74620, d138278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24176 q ha hb
  have h7 (q : Pattern) (ha : d645 q = 1) (hb : d135431 q = 1) : d138280 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d138280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24156 q ha hb
    | true =>
      simp only [d645, d138280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24157 q ha hb
  have h8 (q : Pattern) (ha : d74621 q = 1) (hb : d135431 q = 1) : d138281 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74621, d138281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74621, d138281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74622 q = 1) (hb : d135431 q = 1) : d138282 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74622, d138282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74622, d138282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74623 q = 1) (hb : d135431 q = 1) : d138283 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74623, d138283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74623, d138283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74627 q = 1) (hb : d135431 q = 1) : d138287 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74627, d138287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74627, d138287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24177 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d135431 q = 1) : d138289 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d138289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d138289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24158 q ha hb
  have h13 (q : Pattern) (ha : d74628 q = 1) (hb : d135431 q = 1) : d138290 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74628, d138290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74628, d138290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74629 q = 1) (hb : d135431 q = 1) : d138291 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74629, d138291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74629, d138291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74630 q = 1) (hb : d135431 q = 1) : d138292 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74630, d138292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74630, d138292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74631 q = 1) (hb : d135431 q = 1) : d138293 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74631, d138293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74631, d138293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74636 q = 1) (hb : d135431 q = 1) : d138318 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74636, d138318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74636, d138318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24183 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d135431 q = 1) : d138324 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d138324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d138324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24161 q ha hb
  have h19 (q : Pattern) (ha : d74637 q = 1) (hb : d135431 q = 1) : d138325 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74637, d138325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74637, d138325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74638 q = 1) (hb : d135431 q = 1) : d138326 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74638, d138326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74638, d138326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74639 q = 1) (hb : d135431 q = 1) : d138327 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74639, d138327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74639, d138327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74640 q = 1) (hb : d135431 q = 1) : d138328 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74640, d138328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74640, d138328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74641 q = 1) (hb : d135431 q = 1) : d138329 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74641, d138329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74641, d138329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24185 (p : Pattern) (ha : d74647 p = 1) (hb : d135431 p = 1) : d138335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74642 q = 1) (hb : d135431 q = 1) : d138330 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74642, d138330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74642, d138330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24184 q ha hb
  have h2 (q : Pattern) (ha : d74643 q = 1) (hb : d135431 q = 1) : d138331 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74643, d138331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74643, d138331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74644 q = 1) (hb : d135431 q = 1) : d138332 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74644, d138332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74644, d138332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74645 q = 1) (hb : d135431 q = 1) : d138333 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74645, d138333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74645, d138333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74646 q = 1) (hb : d135431 q = 1) : d138334 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74646, d138334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74646, d138334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74647 q = 1) (hb : d135431 q = 1) : d138335 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74647, d138335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74647, d138335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24186 (p : Pattern) (ha : d769 p = 1) (hb : d135431 p = 1) : d138346 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d756 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d759 q = 1) (hb : d135431 q = 1) : d138337 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d135431, d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d759, d135431, d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
  have h3 (q : Pattern) (ha : d760 q = 1) (hb : d135431 q = 1) : d138338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d761 q = 1) (hb : d135431 q = 1) : d138339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d758 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d94753 q = 1) : d762 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d763 q = 1) (hb : d135431 q = 1) : d138340 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d763, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d764 q = 1) (hb : d135431 q = 1) : d138341 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d765 q = 1) (hb : d135431 q = 1) : d138342 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d766 q = 1) (hb : d135431 q = 1) : d138343 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d766, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d767 q = 1) (hb : d135431 q = 1) : d138344 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d138344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d767, d138344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d768 q = 1) (hb : d135431 q = 1) : d138345 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d768, d138345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d768, d138345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d769 q = 1) (hb : d135431 q = 1) : d138346 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d769, d138346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d769, d138346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro24187 (p : Pattern) (ha : d773 p = 1) (hb : d135431 p = 1) : d138350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d758 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d762 q = 1) (hb : d94753 q = 1) : d762 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d763 q = 1) (hb : d135431 q = 1) : d138340 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d763, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d764 q = 1) (hb : d135431 q = 1) : d138341 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d765 q = 1) (hb : d135431 q = 1) : d138342 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d767 q = 1) (hb : d135431 q = 1) : d138344 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d138344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d767, d138344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d772 q = 1) (hb : d135431 q = 1) : d138349 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d138349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d772, d138349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d773 q = 1) (hb : d135431 q = 1) : d138350 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d138350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d773, d138350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24188 (p : Pattern) (ha : d779 p = 1) (hb : d135431 p = 1) : d138356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24186 q ha hb
    | true =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24187 q ha hb
    | true =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d135431 q = 1) : d138353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d135431 q = 1) : d138354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d778 q = 1) (hb : d135431 q = 1) : d138355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d778, d138355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d778, d138355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d779 q = 1) (hb : d135431 q = 1) : d138356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d779, d138356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d779, d138356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24189 (p : Pattern) (ha : d783 p = 1) (hb : d135431 p = 1) : d138360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24187 q ha hb
    | true =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d135431 q = 1) : d138357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d135431 q = 1) : d138358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d135431 q = 1) : d138359 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d138359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d138359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d135431 q = 1) : d138360 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d138360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d138360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24190 (p : Pattern) (ha : d789 p = 1) (hb : d135431 p = 1) : d138366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d784 q = 1) (hb : d135431 q = 1) : d138361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24188 q ha hb
    | true =>
      simp only [d784, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24189 q ha hb
  have h2 (q : Pattern) (ha : d785 q = 1) (hb : d135431 q = 1) : d138362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d135431 q = 1) : d138363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d786, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d135431 q = 1) : d138364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d135431 q = 1) : d138365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d789 q = 1) (hb : d135431 q = 1) : d138366 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, d138366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, d138366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24191 (p : Pattern) (ha : d792 p = 1) (hb : d135431 p = 1) : d138369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24186 q ha hb
    | true =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24187 q ha hb
    | true =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d135431 q = 1) : d138353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d135431 q = 1) : d138354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d778 q = 1) (hb : d135431 q = 1) : d138355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d778, d138355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d778, d138355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d792 q = 1) (hb : d135431 q = 1) : d138369 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d792, d138369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d792, d138369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24192 (p : Pattern) (ha : d793 p = 1) (hb : d135431 p = 1) : d138370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24187 q ha hb
    | true =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d135431 q = 1) : d138357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d135431 q = 1) : d138358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d135431 q = 1) : d138359 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d138359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d138359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d135431 q = 1) : d138370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d138370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d138370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24193 (p : Pattern) (ha : d799 p = 1) (hb : d135431 p = 1) : d138376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d784 q = 1) (hb : d135431 q = 1) : d138361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24188 q ha hb
    | true =>
      simp only [d784, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24189 q ha hb
  have h2 (q : Pattern) (ha : d785 q = 1) (hb : d135431 q = 1) : d138362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d135431 q = 1) : d138363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d786, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d135431 q = 1) : d138364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d135431 q = 1) : d138365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d794 q = 1) (hb : d135431 q = 1) : d138371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24191 q ha hb
    | true =>
      simp only [d794, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24192 q ha hb
  have h7 (q : Pattern) (ha : d795 q = 1) (hb : d135431 q = 1) : d138372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d796 q = 1) (hb : d135431 q = 1) : d138373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d796, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d797 q = 1) (hb : d135431 q = 1) : d138374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d798 q = 1) (hb : d135431 q = 1) : d138375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d799 q = 1) (hb : d135431 q = 1) : d138376 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, d138376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d799, d138376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24194 (p : Pattern) (ha : d944 p = 1) (hb : d135431 p = 1) : d138456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d784 q = 1) (hb : d135431 q = 1) : d138361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24188 q ha hb
    | true =>
      simp only [d784, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24189 q ha hb
  have h2 (q : Pattern) (ha : d785 q = 1) (hb : d135431 q = 1) : d138362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d135431 q = 1) : d138363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d786, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d135431 q = 1) : d138364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d135431 q = 1) : d138365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d135431 q = 1) : d138451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d138451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24189 q ha hb
    | true =>
      simp only [d939, d138451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d135431 q = 1) : d138452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d138452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d138452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d135431 q = 1) : d138453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d138453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d138453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d135431 q = 1) : d138454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d138454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d138454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d135431 q = 1) : d138455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d138455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d138455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d944 q = 1) (hb : d135431 q = 1) : d138456 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d944, d138456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d944, d138456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24195 (p : Pattern) (ha : d950 p = 1) (hb : d135431 p = 1) : d138462 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d135431 q = 1) : d138451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d138451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24189 q ha hb
    | true =>
      simp only [d939, d138451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d135431 q = 1) : d138452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d138452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d138452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d135431 q = 1) : d138453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d138453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d138453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d135431 q = 1) : d138454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d138454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d138454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d135431 q = 1) : d138455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d138455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d138455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d135431 q = 1) : d138457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d138457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24192 q ha hb
    | true =>
      simp only [d945, d138457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d135431 q = 1) : d138458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d138458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d138458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d135431 q = 1) : d138459 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d138459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d138459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d135431 q = 1) : d138460 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d138460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d138460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d135431 q = 1) : d138461 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d138461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d138461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d135431 q = 1) : d138462 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d138462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d138462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24196 (p : Pattern) (ha : d959 p = 1) (hb : d135431 p = 1) : d138471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d135431 q = 1) : d138457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d138457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24192 q ha hb
    | true =>
      simp only [d945, d138457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d135431 q = 1) : d138458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d138458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d138458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d135431 q = 1) : d138459 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d138459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d138459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d135431 q = 1) : d138460 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d138460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d138460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d135431 q = 1) : d138461 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d138461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d138461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d135431 q = 1) : d138471 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d138471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d138471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24197 (p : Pattern) (ha : d1005 p = 1) (hb : d135431 p = 1) : d138502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d986 q = 1) (hb : d94753 q = 1) : d986 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d987 q = 1) (hb : d135431 q = 1) : d138484 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d987, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d988 q = 1) (hb : d135431 q = 1) : d138485 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d989 q = 1) (hb : d135431 q = 1) : d138486 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d995 q = 1) (hb : d135431 q = 1) : d138492 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d138492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d995, d138492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1004 q = 1) (hb : d135431 q = 1) : d138501 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d138501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1004, d138501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1005 q = 1) (hb : d135431 q = 1) : d138502 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d138502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1005, d138502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24198 (p : Pattern) (ha : d1063 p = 1) (hb : d135431 p = 1) : d138533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d135431 q = 1) : d138503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d138503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24197 q ha hb
    | true =>
      simp only [d1006, d138503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d135431 q = 1) : d138504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d138504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d138504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d135431 q = 1) : d138530 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d138530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d138530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d135431 q = 1) : d138531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d138531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d138531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d135431 q = 1) : d138532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d138532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d138532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d135431 q = 1) : d138533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d138533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d138533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24199 (p : Pattern) (ha : d1069 p = 1) (hb : d135431 p = 1) : d138539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d135431 q = 1) : d138534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d138534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24198 q ha hb
    | true =>
      simp only [d1064, d138534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d135431 q = 1) : d138535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d138535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d138535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d135431 q = 1) : d138536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d138536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d138536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d135431 q = 1) : d138537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d138537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d138537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d135431 q = 1) : d138538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d138538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d138538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d135431 q = 1) : d138539 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d138539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d138539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24200 (p : Pattern) (ha : d804 p = 1) (hb : d135431 p = 1) : d138381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24186 q ha hb
    | true =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24187 q ha hb
    | true =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d135431 q = 1) : d138353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d135431 q = 1) : d138354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d803 q = 1) (hb : d135431 q = 1) : d138380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d138380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d803, d138380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d804 q = 1) (hb : d135431 q = 1) : d138381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d804, d138381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d804, d138381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24201 (p : Pattern) (ha : d806 p = 1) (hb : d135431 p = 1) : d138383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24187 q ha hb
    | true =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d135431 q = 1) : d138357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d135431 q = 1) : d138358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d135431 q = 1) : d138382 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d138382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d138382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d135431 q = 1) : d138383 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d138383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d138383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24202 (p : Pattern) (ha : d813 p = 1) (hb : d135431 p = 1) : d138390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24186 q ha hb
    | true =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24187 q ha hb
    | true =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d135431 q = 1) : d138353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d811 q = 1) (hb : d135431 q = 1) : d138388 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d138388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d138388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d812 q = 1) (hb : d135431 q = 1) : d138389 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d138389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d812, d138389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d813 q = 1) (hb : d135431 q = 1) : d138390 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d813, d138390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d813, d138390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24203 (p : Pattern) (ha : d816 p = 1) (hb : d135431 p = 1) : d138393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24187 q ha hb
    | true =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d135431 q = 1) : d138357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d135431 q = 1) : d138391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d138391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d138391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d135431 q = 1) : d138392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d138392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d138392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d135431 q = 1) : d138393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d138393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d138393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24204 (p : Pattern) (ha : d845 p = 1) (hb : d135431 p = 1) : d138402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d839 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d840 q = 1) (hb : d135431 q = 1) : d138397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d840, d135431, d138397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d840, d135431, d138397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12510 q ha hb
  have h3 (q : Pattern) (ha : d841 q = 1) (hb : d135431 q = 1) : d138398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d841, d138398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d841, d138398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d842 q = 1) (hb : d135431 q = 1) : d138399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d842, d138399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d842, d138399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d756 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d759 q = 1) (hb : d135431 q = 1) : d138337 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d135431, d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d759, d135431, d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
  have h7 (q : Pattern) (ha : d760 q = 1) (hb : d135431 q = 1) : d138338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d761 q = 1) (hb : d135431 q = 1) : d138339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d843 q = 1) (hb : d135431 q = 1) : d138400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d843, d138400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d843, d138400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d758 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d762 q = 1) (hb : d94753 q = 1) : d762 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d763 q = 1) (hb : d135431 q = 1) : d138340 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d763, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d764 q = 1) (hb : d135431 q = 1) : d138341 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d765 q = 1) (hb : d135431 q = 1) : d138342 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d766 q = 1) (hb : d135431 q = 1) : d138343 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d766, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d844 q = 1) (hb : d135431 q = 1) : d138401 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d844, d138401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d844, d138401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d845 q = 1) (hb : d135431 q = 1) : d138402 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d845, d138402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d845, d138402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro24205 (p : Pattern) (ha : d851 p = 1) (hb : d135431 p = 1) : d138408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d846 q = 1) (hb : d135431 q = 1) : d138403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d138403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24204 q ha hb
    | true =>
      simp only [d846, d138403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d847 q = 1) (hb : d135431 q = 1) : d138404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d138404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d847, d138404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d770 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24186 q ha hb
    | true =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d771 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d848 q = 1) (hb : d135431 q = 1) : d138405 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d848, d138405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d848, d138405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d849 q = 1) (hb : d135431 q = 1) : d138406 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d849, d138406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d849, d138406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d850 q = 1) (hb : d135431 q = 1) : d138407 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d850, d138407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d850, d138407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d851 q = 1) (hb : d135431 q = 1) : d138408 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d851, d138408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d851, d138408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24206 (p : Pattern) (ha : d5463 p = 1) (hb : d135431 p = 1) : d138416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d756 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d759 q = 1) (hb : d135431 q = 1) : d138337 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d135431, d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d759, d135431, d138337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
  have h3 (q : Pattern) (ha : d760 q = 1) (hb : d135431 q = 1) : d138338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d138338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d761 q = 1) (hb : d135431 q = 1) : d138339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d138339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d758 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d94753 q = 1) : d762 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d763 q = 1) (hb : d135431 q = 1) : d138340 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d763, d135431, d138340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d764 q = 1) (hb : d135431 q = 1) : d138341 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d138341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d765 q = 1) (hb : d135431 q = 1) : d138342 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d138342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d766 q = 1) (hb : d135431 q = 1) : d138343 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d766, d138343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d5456 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d5457 q = 1) (hb : d94753 q = 1) : d5457 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d5458 q = 1) (hb : d135431 q = 1) : d138411 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5458, d135431, d138411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d5458, d135431, d138411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5459 q = 1) (hb : d135431 q = 1) : d138412 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5459, d138412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5459, d138412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d5460 q = 1) (hb : d135431 q = 1) : d138413 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5460, d138413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5460, d138413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5461 q = 1) (hb : d135431 q = 1) : d138414 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5461, d138414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5461, d138414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d5462 q = 1) (hb : d135431 q = 1) : d138415 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5462, d138415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5462, d138415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d5463 q = 1) (hb : d135431 q = 1) : d138416 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5463, d138416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d5463, d138416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro24207 (p : Pattern) (ha : d5469 p = 1) (hb : d135431 p = 1) : d138422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5464 q = 1) (hb : d135431 q = 1) : d138417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5464, d138417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24206 q ha hb
    | true =>
      simp only [d5464, d138417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5465 q = 1) (hb : d135431 q = 1) : d138418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5465, d138418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5465, d138418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5466 q = 1) (hb : d135431 q = 1) : d138419 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5466, d138419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5466, d138419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5467 q = 1) (hb : d135431 q = 1) : d138420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5467, d138420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5467, d138420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5468 q = 1) (hb : d135431 q = 1) : d138421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5468, d138421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5468, d138421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5469 q = 1) (hb : d135431 q = 1) : d138422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5469, d138422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5469, d138422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24208 (p : Pattern) (ha : d74652 p = 1) (hb : d135431 p = 1) : d138428 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d807 q = 1) (hb : d135431 q = 1) : d138384 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d138384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24200 q ha hb
    | true =>
      simp only [d807, d138384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24201 q ha hb
  have h2 (q : Pattern) (ha : d808 q = 1) (hb : d135431 q = 1) : d138385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d138385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d138385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d135431 q = 1) : d138386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d138386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d809, d138386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d135431 q = 1) : d138387 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d138387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d138387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d817 q = 1) (hb : d135431 q = 1) : d138394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d138394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24202 q ha hb
    | true =>
      simp only [d817, d138394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24203 q ha hb
  have h6 (q : Pattern) (ha : d818 q = 1) (hb : d135431 q = 1) : d138395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d138395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d138395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d819 q = 1) (hb : d135431 q = 1) : d138396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d138396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d819, d138396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d852 q = 1) (hb : d135431 q = 1) : d138409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d138409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24205 q ha hb
    | true =>
      simp only [d852, d138409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24188 q ha hb
  have h9 (q : Pattern) (ha : d4446 q = 1) (hb : d135431 q = 1) : d138410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d138410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4446, d138410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5470 q = 1) (hb : d135431 q = 1) : d138423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5470, d138423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24207 q ha hb
    | true =>
      simp only [d5470, d138423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5471 q = 1) (hb : d135431 q = 1) : d138424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5471, d138424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5471, d138424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74649 q = 1) (hb : d135431 q = 1) : d138425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74649, d138425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74649, d138425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74650 q = 1) (hb : d135431 q = 1) : d138426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74650, d138426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74650, d138426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74651 q = 1) (hb : d135431 q = 1) : d138427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74651, d138427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74651, d138427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74652 q = 1) (hb : d135431 q = 1) : d138428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74652, d138428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74652, d138428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24209 (p : Pattern) (ha : d915 p = 1) (hb : d135431 p = 1) : d138429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24186 q ha hb
    | true =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24187 q ha hb
    | true =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d135431 q = 1) : d138353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d135431 q = 1) : d138354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d138354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d803 q = 1) (hb : d135431 q = 1) : d138380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d138380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d803, d138380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d915 q = 1) (hb : d135431 q = 1) : d138429 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d915, d138429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d915, d138429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24210 (p : Pattern) (ha : d916 p = 1) (hb : d135431 p = 1) : d138430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24187 q ha hb
    | true =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d135431 q = 1) : d138357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d135431 q = 1) : d138358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d138358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d135431 q = 1) : d138382 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d138382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d138382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d135431 q = 1) : d138430 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d138430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d138430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24211 (p : Pattern) (ha : d921 p = 1) (hb : d135431 p = 1) : d138435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24186 q ha hb
    | true =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24187 q ha hb
    | true =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d135431 q = 1) : d138353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d138353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d811 q = 1) (hb : d135431 q = 1) : d138388 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d138388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d138388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d812 q = 1) (hb : d135431 q = 1) : d138389 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d138389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d812, d138389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d921 q = 1) (hb : d135431 q = 1) : d138435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d921, d138435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d921, d138435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24212 (p : Pattern) (ha : d922 p = 1) (hb : d135431 p = 1) : d138436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d135431 q = 1) : d138351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24187 q ha hb
    | true =>
      simp only [d774, d138351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d135431 q = 1) : d138352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d138352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d135431 q = 1) : d138357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d138357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d135431 q = 1) : d138391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d138391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d138391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d135431 q = 1) : d138392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d138392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d138392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d135431 q = 1) : d138436 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d138436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d138436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24213 (p : Pattern) (ha : d926 p = 1) (hb : d135431 p = 1) : d138440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d846 q = 1) (hb : d135431 q = 1) : d138403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d138403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24204 q ha hb
    | true =>
      simp only [d846, d138403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d847 q = 1) (hb : d135431 q = 1) : d138404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d138404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d847, d138404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d770 q = 1) (hb : d135431 q = 1) : d138347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24186 q ha hb
    | true =>
      simp only [d770, d138347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d771 q = 1) (hb : d135431 q = 1) : d138348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d138348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d848 q = 1) (hb : d135431 q = 1) : d138405 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d848, d138405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d848, d138405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d849 q = 1) (hb : d135431 q = 1) : d138406 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d849, d138406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d849, d138406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d850 q = 1) (hb : d135431 q = 1) : d138407 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d850, d138407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d850, d138407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d926 q = 1) (hb : d135431 q = 1) : d138440 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d926, d138440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d926, d138440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24214 (p : Pattern) (ha : d5476 p = 1) (hb : d135431 p = 1) : d138443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5464 q = 1) (hb : d135431 q = 1) : d138417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5464, d138417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24206 q ha hb
    | true =>
      simp only [d5464, d138417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5465 q = 1) (hb : d135431 q = 1) : d138418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5465, d138418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5465, d138418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5466 q = 1) (hb : d135431 q = 1) : d138419 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5466, d138419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5466, d138419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5467 q = 1) (hb : d135431 q = 1) : d138420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5467, d138420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5467, d138420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5468 q = 1) (hb : d135431 q = 1) : d138421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5468, d138421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5468, d138421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5476 q = 1) (hb : d135431 q = 1) : d138443 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5476, d138443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5476, d138443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24215 (p : Pattern) (ha : d74656 p = 1) (hb : d135431 p = 1) : d138449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d807 q = 1) (hb : d135431 q = 1) : d138384 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d138384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24200 q ha hb
    | true =>
      simp only [d807, d138384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24201 q ha hb
  have h2 (q : Pattern) (ha : d808 q = 1) (hb : d135431 q = 1) : d138385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d138385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d138385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d135431 q = 1) : d138386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d138386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d809, d138386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d135431 q = 1) : d138387 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d138387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d138387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d817 q = 1) (hb : d135431 q = 1) : d138394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d138394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24202 q ha hb
    | true =>
      simp only [d817, d138394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24203 q ha hb
  have h6 (q : Pattern) (ha : d818 q = 1) (hb : d135431 q = 1) : d138395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d138395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d138395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d819 q = 1) (hb : d135431 q = 1) : d138396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d138396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d819, d138396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d852 q = 1) (hb : d135431 q = 1) : d138409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d138409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24205 q ha hb
    | true =>
      simp only [d852, d138409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24188 q ha hb
  have h9 (q : Pattern) (ha : d4446 q = 1) (hb : d135431 q = 1) : d138410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d138410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4446, d138410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5470 q = 1) (hb : d135431 q = 1) : d138423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5470, d138423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24207 q ha hb
    | true =>
      simp only [d5470, d138423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5471 q = 1) (hb : d135431 q = 1) : d138424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5471, d138424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5471, d138424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74649 q = 1) (hb : d135431 q = 1) : d138425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74649, d138425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74649, d138425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74650 q = 1) (hb : d135431 q = 1) : d138426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74650, d138426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74650, d138426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74651 q = 1) (hb : d135431 q = 1) : d138427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74651, d138427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74651, d138427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d917 q = 1) (hb : d135431 q = 1) : d138431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d917, d138431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24209 q ha hb
    | true =>
      simp only [d917, d138431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24210 q ha hb
  have h16 (q : Pattern) (ha : d918 q = 1) (hb : d135431 q = 1) : d138432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, d138432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d918, d138432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d919 q = 1) (hb : d135431 q = 1) : d138433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d138433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d919, d138433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d920 q = 1) (hb : d135431 q = 1) : d138434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, d138434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, d138434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d923 q = 1) (hb : d135431 q = 1) : d138437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, d138437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24211 q ha hb
    | true =>
      simp only [d923, d138437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24212 q ha hb
  have h20 (q : Pattern) (ha : d924 q = 1) (hb : d135431 q = 1) : d138438 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d138438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d924, d138438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d925 q = 1) (hb : d135431 q = 1) : d138439 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d138439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d925, d138439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d927 q = 1) (hb : d135431 q = 1) : d138441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d138441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24213 q ha hb
    | true =>
      simp only [d927, d138441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24191 q ha hb
  have h23 (q : Pattern) (ha : d4451 q = 1) (hb : d135431 q = 1) : d138442 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d138442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4451, d138442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5477 q = 1) (hb : d135431 q = 1) : d138444 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5477, d138444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24214 q ha hb
    | true =>
      simp only [d5477, d138444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5478 q = 1) (hb : d135431 q = 1) : d138445 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5478, d138445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5478, d138445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74653 q = 1) (hb : d135431 q = 1) : d138446 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74653, d138446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74653, d138446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74654 q = 1) (hb : d135431 q = 1) : d138447 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74654, d138447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74654, d138447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74655 q = 1) (hb : d135431 q = 1) : d138448 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74655, d138448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74655, d138448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74656 q = 1) (hb : d135431 q = 1) : d138449 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74656, d138449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74656, d138449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro24216 (p : Pattern) (ha : d74663 p = 1) (hb : d135431 p = 1) : d138469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d927 q = 1) (hb : d135431 q = 1) : d138441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d138441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24213 q ha hb
    | true =>
      simp only [d927, d138441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24191 q ha hb
  have h2 (q : Pattern) (ha : d4451 q = 1) (hb : d135431 q = 1) : d138442 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d138442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4451, d138442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5477 q = 1) (hb : d135431 q = 1) : d138444 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5477, d138444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24214 q ha hb
    | true =>
      simp only [d5477, d138444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5478 q = 1) (hb : d135431 q = 1) : d138445 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5478, d138445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5478, d138445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74653 q = 1) (hb : d135431 q = 1) : d138446 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74653, d138446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74653, d138446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74661 q = 1) (hb : d135431 q = 1) : d138467 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74661, d138467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74661, d138467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74662 q = 1) (hb : d135431 q = 1) : d138468 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74662, d138468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74662, d138468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74663 q = 1) (hb : d135431 q = 1) : d138469 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74663, d138469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74663, d138469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24217 (p : Pattern) (ha : d992 p = 1) (hb : d135431 p = 1) : d138489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d970 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d977 q = 1) (hb : d135431 q = 1) : d138477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d135431, d138477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d977, d135431, d138477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12527 q ha hb
  have h3 (q : Pattern) (ha : d978 q = 1) (hb : d135431 q = 1) : d138478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d138478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d978, d138478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d979 q = 1) (hb : d135431 q = 1) : d138479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d138479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d979, d138479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d976 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d982 q = 1) (hb : d135431 q = 1) : d138480 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d135431, d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d982, d135431, d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
  have h7 (q : Pattern) (ha : d983 q = 1) (hb : d135431 q = 1) : d138481 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d984 q = 1) (hb : d135431 q = 1) : d138482 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d985 q = 1) (hb : d135431 q = 1) : d138483 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d985, d138483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d985, d138483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d986 q = 1) (hb : d94753 q = 1) : d986 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d987 q = 1) (hb : d135431 q = 1) : d138484 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d987, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d988 q = 1) (hb : d135431 q = 1) : d138485 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d989 q = 1) (hb : d135431 q = 1) : d138486 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d990 q = 1) (hb : d135431 q = 1) : d138487 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d990, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d991 q = 1) (hb : d135431 q = 1) : d138488 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d991, d138488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d991, d138488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d992 q = 1) (hb : d135431 q = 1) : d138489 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d992, d138489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d992, d138489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro24218 (p : Pattern) (ha : d997 p = 1) (hb : d135431 p = 1) : d138494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d976 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d982 q = 1) (hb : d135431 q = 1) : d138480 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d135431, d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d982, d135431, d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
  have h3 (q : Pattern) (ha : d983 q = 1) (hb : d135431 q = 1) : d138481 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d984 q = 1) (hb : d135431 q = 1) : d138482 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d986 q = 1) (hb : d94753 q = 1) : d986 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d987 q = 1) (hb : d135431 q = 1) : d138484 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d987, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d988 q = 1) (hb : d135431 q = 1) : d138485 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d989 q = 1) (hb : d135431 q = 1) : d138486 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d990 q = 1) (hb : d135431 q = 1) : d138487 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d990, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d995 q = 1) (hb : d135431 q = 1) : d138492 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d138492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d995, d138492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d996 q = 1) (hb : d135431 q = 1) : d138493 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d996, d138493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d996, d138493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d997 q = 1) (hb : d135431 q = 1) : d138494 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d997, d138494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d997, d138494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro24219 (p : Pattern) (ha : d1003 p = 1) (hb : d135431 p = 1) : d138500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d993 q = 1) (hb : d135431 q = 1) : d138490 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d993, d138490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24217 q ha hb
    | true =>
      simp only [d993, d138490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d994 q = 1) (hb : d135431 q = 1) : d138491 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d994, d138491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d994, d138491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d998 q = 1) (hb : d135431 q = 1) : d138495 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24218 q ha hb
    | true =>
      simp only [d998, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d999 q = 1) (hb : d135431 q = 1) : d138496 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1000 q = 1) (hb : d135431 q = 1) : d138497 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1000, d138497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1000, d138497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1001 q = 1) (hb : d135431 q = 1) : d138498 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1001, d138498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1001, d138498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1002 q = 1) (hb : d135431 q = 1) : d138499 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1002, d138499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1002, d138499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1003 q = 1) (hb : d135431 q = 1) : d138500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1003, d138500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1003, d138500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24220 (p : Pattern) (ha : d1011 p = 1) (hb : d135431 p = 1) : d138508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d998 q = 1) (hb : d135431 q = 1) : d138495 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24218 q ha hb
    | true =>
      simp only [d998, d138495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d135431 q = 1) : d138496 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d138496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d135431 q = 1) : d138503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d138503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24197 q ha hb
    | true =>
      simp only [d1006, d138503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d135431 q = 1) : d138504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d138504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d138504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1008 q = 1) (hb : d135431 q = 1) : d138505 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1008, d138505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1008, d138505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1009 q = 1) (hb : d135431 q = 1) : d138506 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1009, d138506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1009, d138506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1010 q = 1) (hb : d135431 q = 1) : d138507 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1010, d138507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1010, d138507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1011 q = 1) (hb : d135431 q = 1) : d138508 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1011, d138508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1011, d138508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24221 (p : Pattern) (ha : d5507 p = 1) (hb : d135431 p = 1) : d138516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d976 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d982 q = 1) (hb : d135431 q = 1) : d138480 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d135431, d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d982, d135431, d138480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
  have h3 (q : Pattern) (ha : d983 q = 1) (hb : d135431 q = 1) : d138481 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d138481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d984 q = 1) (hb : d135431 q = 1) : d138482 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d138482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d986 q = 1) (hb : d94753 q = 1) : d986 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d987 q = 1) (hb : d135431 q = 1) : d138484 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d987, d135431, d138484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d988 q = 1) (hb : d135431 q = 1) : d138485 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d138485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d989 q = 1) (hb : d135431 q = 1) : d138486 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d138486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d990 q = 1) (hb : d135431 q = 1) : d138487 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d990, d138487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d5500 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d5501 q = 1) (hb : d94753 q = 1) : d5501 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d5502 q = 1) (hb : d135431 q = 1) : d138511 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5502, d135431, d138511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d5502, d135431, d138511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5503 q = 1) (hb : d135431 q = 1) : d138512 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5503, d138512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5503, d138512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d5504 q = 1) (hb : d135431 q = 1) : d138513 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5504, d138513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5504, d138513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5505 q = 1) (hb : d135431 q = 1) : d138514 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5505, d138514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5505, d138514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d5506 q = 1) (hb : d135431 q = 1) : d138515 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5506, d138515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5506, d138515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d5507 q = 1) (hb : d135431 q = 1) : d138516 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5507, d138516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d5507, d138516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro24222 (p : Pattern) (ha : d5513 p = 1) (hb : d135431 p = 1) : d138522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5508 q = 1) (hb : d135431 q = 1) : d138517 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5508, d138517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24221 q ha hb
    | true =>
      simp only [d5508, d138517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5509 q = 1) (hb : d135431 q = 1) : d138518 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5509, d138518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5509, d138518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5510 q = 1) (hb : d135431 q = 1) : d138519 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5510, d138519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5510, d138519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5511 q = 1) (hb : d135431 q = 1) : d138520 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5511, d138520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5511, d138520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5512 q = 1) (hb : d135431 q = 1) : d138521 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5512, d138521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5512, d138521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5513 q = 1) (hb : d135431 q = 1) : d138522 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5513, d138522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5513, d138522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24223 (p : Pattern) (ha : d74672 p = 1) (hb : d135431 p = 1) : d138528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1012 q = 1) (hb : d135431 q = 1) : d138509 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1012, d138509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24219 q ha hb
    | true =>
      simp only [d1012, d138509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24220 q ha hb
  have h2 (q : Pattern) (ha : d4466 q = 1) (hb : d135431 q = 1) : d138510 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d138510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4466, d138510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5514 q = 1) (hb : d135431 q = 1) : d138523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5514, d138523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24222 q ha hb
    | true =>
      simp only [d5514, d138523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5515 q = 1) (hb : d135431 q = 1) : d138524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5515, d138524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5515, d138524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74669 q = 1) (hb : d135431 q = 1) : d138525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74669, d138525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74669, d138525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74670 q = 1) (hb : d135431 q = 1) : d138526 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74670, d138526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74670, d138526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74671 q = 1) (hb : d135431 q = 1) : d138527 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74671, d138527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74671, d138527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74672 q = 1) (hb : d135431 q = 1) : d138528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74672, d138528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74672, d138528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24224 (p : Pattern) (ha : d74678 p = 1) (hb : d135431 p = 1) : d138545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d135431 q = 1) : d138367 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d138367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d138367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24190 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d135431 q = 1) : d138368 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d138368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d138368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d135431 q = 1) : d138377 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d138377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24190 q ha hb
    | true =>
      simp only [d800, d138377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24193 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d135431 q = 1) : d138378 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d138378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d138378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d135431 q = 1) : d138379 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d138379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d138379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74657 q = 1) (hb : d135431 q = 1) : d138450 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74657, d138450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24208 q ha hb
    | true =>
      simp only [d74657, d138450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24215 q ha hb
  have h7 (q : Pattern) (ha : d951 q = 1) (hb : d135431 q = 1) : d138463 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d138463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24194 q ha hb
    | true =>
      simp only [d951, d138463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24195 q ha hb
  have h8 (q : Pattern) (ha : d74658 q = 1) (hb : d135431 q = 1) : d138464 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74658, d138464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74658, d138464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74659 q = 1) (hb : d135431 q = 1) : d138465 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74659, d138465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74659, d138465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74660 q = 1) (hb : d135431 q = 1) : d138466 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74660, d138466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74660, d138466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74664 q = 1) (hb : d135431 q = 1) : d138470 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74664, d138470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74664, d138470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24216 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d135431 q = 1) : d138472 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d138472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d138472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24196 q ha hb
  have h13 (q : Pattern) (ha : d74665 q = 1) (hb : d135431 q = 1) : d138473 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74665, d138473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74665, d138473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74666 q = 1) (hb : d135431 q = 1) : d138474 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74666, d138474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74666, d138474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74667 q = 1) (hb : d135431 q = 1) : d138475 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74667, d138475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74667, d138475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74668 q = 1) (hb : d135431 q = 1) : d138476 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74668, d138476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74668, d138476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74673 q = 1) (hb : d135431 q = 1) : d138529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74673, d138529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74673, d138529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24223 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d135431 q = 1) : d138540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d138540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d138540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24199 q ha hb
  have h19 (q : Pattern) (ha : d74674 q = 1) (hb : d135431 q = 1) : d138541 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74674, d138541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74674, d138541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74675 q = 1) (hb : d135431 q = 1) : d138542 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74675, d138542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74675, d138542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74676 q = 1) (hb : d135431 q = 1) : d138543 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74676, d138543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74676, d138543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74677 q = 1) (hb : d135431 q = 1) : d138544 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74677, d138544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74677, d138544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74678 q = 1) (hb : d135431 q = 1) : d138545 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74678, d138545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74678, d138545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24225 (p : Pattern) (ha : d74684 p = 1) (hb : d135431 p = 1) : d138551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74679 q = 1) (hb : d135431 q = 1) : d138546 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74679, d138546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74679, d138546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24224 q ha hb
  have h2 (q : Pattern) (ha : d74680 q = 1) (hb : d135431 q = 1) : d138547 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74680, d138547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74680, d138547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74681 q = 1) (hb : d135431 q = 1) : d138548 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74681, d138548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74681, d138548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74682 q = 1) (hb : d135431 q = 1) : d138549 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74682, d138549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74682, d138549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74683 q = 1) (hb : d135431 q = 1) : d138550 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74683, d138550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74683, d138550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74684 q = 1) (hb : d135431 q = 1) : d138551 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74684, d138551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74684, d138551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24226 (p : Pattern) (ha : d1148 p = 1) (hb : d135431 p = 1) : d138563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1129 q = 1) (hb : d135431 q = 1) : d138554 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d135431, d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1129, d135431, d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
  have h3 (q : Pattern) (ha : d1130 q = 1) (hb : d135431 q = 1) : d138555 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1131 q = 1) (hb : d135431 q = 1) : d138556 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1142 q = 1) (hb : d135431 q = 1) : d138557 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d135431, d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1142, d135431, d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12537 q ha hb
  have h7 (q : Pattern) (ha : d1143 q = 1) (hb : d135431 q = 1) : d138558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1144 q = 1) (hb : d135431 q = 1) : d138559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1145 q = 1) (hb : d135431 q = 1) : d138560 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d138560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1145, d138560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1146 q = 1) (hb : d135431 q = 1) : d138561 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d138561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1146, d138561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1147 q = 1) (hb : d135431 q = 1) : d138562 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1147, d138562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1147, d138562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1148 q = 1) (hb : d135431 q = 1) : d138563 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1148, d138563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1148, d138563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro24227 (p : Pattern) (ha : d1152 p = 1) (hb : d135431 p = 1) : d138567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1142 q = 1) (hb : d135431 q = 1) : d138557 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d135431, d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1142, d135431, d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12537 q ha hb
  have h3 (q : Pattern) (ha : d1143 q = 1) (hb : d135431 q = 1) : d138558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1144 q = 1) (hb : d135431 q = 1) : d138559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1146 q = 1) (hb : d135431 q = 1) : d138561 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d138561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1146, d138561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1151 q = 1) (hb : d135431 q = 1) : d138566 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1151, d138566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1151, d138566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1152 q = 1) (hb : d135431 q = 1) : d138567 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1152, d138567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1152, d138567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24228 (p : Pattern) (ha : d1158 p = 1) (hb : d135431 p = 1) : d138573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d135431 q = 1) : d138564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24226 q ha hb
    | true =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d135431 q = 1) : d138565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24227 q ha hb
    | true =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d135431 q = 1) : d138570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d135431 q = 1) : d138571 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1157 q = 1) (hb : d135431 q = 1) : d138572 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d138572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1157, d138572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1158 q = 1) (hb : d135431 q = 1) : d138573 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1158, d138573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1158, d138573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24229 (p : Pattern) (ha : d1162 p = 1) (hb : d135431 p = 1) : d138577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24227 q ha hb
    | true =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d135431 q = 1) : d138574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d135431 q = 1) : d138575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d135431 q = 1) : d138576 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d138576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d138576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1162 q = 1) (hb : d135431 q = 1) : d138577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, d138577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, d138577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24230 (p : Pattern) (ha : d1168 p = 1) (hb : d135431 p = 1) : d138583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d135431 q = 1) : d138578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24228 q ha hb
    | true =>
      simp only [d1163, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24229 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d135431 q = 1) : d138579 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d135431 q = 1) : d138580 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d135431 q = 1) : d138581 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d135431 q = 1) : d138582 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1168 q = 1) (hb : d135431 q = 1) : d138583 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, d138583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, d138583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24231 (p : Pattern) (ha : d1171 p = 1) (hb : d135431 p = 1) : d138586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d135431 q = 1) : d138564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24226 q ha hb
    | true =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d135431 q = 1) : d138565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24227 q ha hb
    | true =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d135431 q = 1) : d138570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d135431 q = 1) : d138571 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1157 q = 1) (hb : d135431 q = 1) : d138572 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d138572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1157, d138572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1171 q = 1) (hb : d135431 q = 1) : d138586 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1171, d138586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1171, d138586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24232 (p : Pattern) (ha : d1172 p = 1) (hb : d135431 p = 1) : d138587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24227 q ha hb
    | true =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d135431 q = 1) : d138574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d135431 q = 1) : d138575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d135431 q = 1) : d138576 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d138576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d138576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1172 q = 1) (hb : d135431 q = 1) : d138587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, d138587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1172, d138587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24233 (p : Pattern) (ha : d1178 p = 1) (hb : d135431 p = 1) : d138593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d135431 q = 1) : d138578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24228 q ha hb
    | true =>
      simp only [d1163, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24229 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d135431 q = 1) : d138579 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d135431 q = 1) : d138580 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d135431 q = 1) : d138581 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d135431 q = 1) : d138582 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1173 q = 1) (hb : d135431 q = 1) : d138588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d138588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24231 q ha hb
    | true =>
      simp only [d1173, d138588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24232 q ha hb
  have h7 (q : Pattern) (ha : d1174 q = 1) (hb : d135431 q = 1) : d138589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d138589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d138589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1175 q = 1) (hb : d135431 q = 1) : d138590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d138590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1175, d138590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1176 q = 1) (hb : d135431 q = 1) : d138591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d138591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d138591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1177 q = 1) (hb : d135431 q = 1) : d138592 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d138592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d138592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1178 q = 1) (hb : d135431 q = 1) : d138593 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, d138593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1178, d138593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24234 (p : Pattern) (ha : d1355 p = 1) (hb : d135431 p = 1) : d138673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d135431 q = 1) : d138578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24228 q ha hb
    | true =>
      simp only [d1163, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24229 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d135431 q = 1) : d138579 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d135431 q = 1) : d138580 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d135431 q = 1) : d138581 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d135431 q = 1) : d138582 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d135431 q = 1) : d138668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d138668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24229 q ha hb
    | true =>
      simp only [d1350, d138668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d135431 q = 1) : d138669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d138669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d138669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d135431 q = 1) : d138670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d138670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d138670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d135431 q = 1) : d138671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d138671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d138671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d135431 q = 1) : d138672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d138672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d138672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1355 q = 1) (hb : d135431 q = 1) : d138673 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1355, d138673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1355, d138673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24235 (p : Pattern) (ha : d1361 p = 1) (hb : d135431 p = 1) : d138679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d135431 q = 1) : d138668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d138668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24229 q ha hb
    | true =>
      simp only [d1350, d138668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d135431 q = 1) : d138669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d138669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d138669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d135431 q = 1) : d138670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d138670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, d138670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d135431 q = 1) : d138671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d138671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d138671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d135431 q = 1) : d138672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d138672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d138672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1356 q = 1) (hb : d135431 q = 1) : d138674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d138674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24232 q ha hb
    | true =>
      simp only [d1356, d138674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1357 q = 1) (hb : d135431 q = 1) : d138675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d138675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d138675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1358 q = 1) (hb : d135431 q = 1) : d138676 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d138676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1358, d138676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1359 q = 1) (hb : d135431 q = 1) : d138677 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d138677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d138677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1360 q = 1) (hb : d135431 q = 1) : d138678 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d138678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d138678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1361 q = 1) (hb : d135431 q = 1) : d138679 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, d138679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1361, d138679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24236 (p : Pattern) (ha : d1370 p = 1) (hb : d135431 p = 1) : d138688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1356 q = 1) (hb : d135431 q = 1) : d138674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d138674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24232 q ha hb
    | true =>
      simp only [d1356, d138674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1357 q = 1) (hb : d135431 q = 1) : d138675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d138675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d138675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1358 q = 1) (hb : d135431 q = 1) : d138676 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d138676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1358, d138676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1359 q = 1) (hb : d135431 q = 1) : d138677 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d138677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d138677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1360 q = 1) (hb : d135431 q = 1) : d138678 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d138678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d138678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1370 q = 1) (hb : d135431 q = 1) : d138688 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, d138688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, d138688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24237 (p : Pattern) (ha : d1430 p = 1) (hb : d135431 p = 1) : d138719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1412 q = 1) (hb : d135431 q = 1) : d138701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d135431, d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1412, d135431, d138701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12574 q ha hb
  have h3 (q : Pattern) (ha : d1413 q = 1) (hb : d135431 q = 1) : d138702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d138702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1414 q = 1) (hb : d135431 q = 1) : d138703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d138703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1420 q = 1) (hb : d135431 q = 1) : d138709 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d138709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1420, d138709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1429 q = 1) (hb : d135431 q = 1) : d138718 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1429, d138718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1429, d138718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1430 q = 1) (hb : d135431 q = 1) : d138719 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1430, d138719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1430, d138719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24238 (p : Pattern) (ha : d1497 p = 1) (hb : d135431 p = 1) : d138750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1431 q = 1) (hb : d135431 q = 1) : d138720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24237 q ha hb
    | true =>
      simp only [d1431, d138720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1432 q = 1) (hb : d135431 q = 1) : d138721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d138721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1494 q = 1) (hb : d135431 q = 1) : d138747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, d138747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1494, d138747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1495 q = 1) (hb : d135431 q = 1) : d138748 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, d138748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1495, d138748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1496 q = 1) (hb : d135431 q = 1) : d138749 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, d138749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1496, d138749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1497 q = 1) (hb : d135431 q = 1) : d138750 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, d138750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1497, d138750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24239 (p : Pattern) (ha : d1503 p = 1) (hb : d135431 p = 1) : d138756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1498 q = 1) (hb : d135431 q = 1) : d138751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, d138751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24238 q ha hb
    | true =>
      simp only [d1498, d138751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1499 q = 1) (hb : d135431 q = 1) : d138752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, d138752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1499, d138752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1500 q = 1) (hb : d135431 q = 1) : d138753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, d138753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1500, d138753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1501 q = 1) (hb : d135431 q = 1) : d138754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, d138754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, d138754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1502 q = 1) (hb : d135431 q = 1) : d138755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, d138755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, d138755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1503 q = 1) (hb : d135431 q = 1) : d138756 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, d138756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, d138756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24240 (p : Pattern) (ha : d1183 p = 1) (hb : d135431 p = 1) : d138598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d135431 q = 1) : d138564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24226 q ha hb
    | true =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d135431 q = 1) : d138565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24227 q ha hb
    | true =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d135431 q = 1) : d138570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d135431 q = 1) : d138571 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1182 q = 1) (hb : d135431 q = 1) : d138597 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d138597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d138597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1183 q = 1) (hb : d135431 q = 1) : d138598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1183, d138598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1183, d138598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24241 (p : Pattern) (ha : d1185 p = 1) (hb : d135431 p = 1) : d138600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24227 q ha hb
    | true =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d135431 q = 1) : d138574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d135431 q = 1) : d138575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d138575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d135431 q = 1) : d138599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d138599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d138599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1185 q = 1) (hb : d135431 q = 1) : d138600 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, d138600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, d138600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24242 (p : Pattern) (ha : d1192 p = 1) (hb : d135431 p = 1) : d138607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d135431 q = 1) : d138564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24226 q ha hb
    | true =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d135431 q = 1) : d138565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24227 q ha hb
    | true =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d135431 q = 1) : d138570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1190 q = 1) (hb : d135431 q = 1) : d138605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d138605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d138605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1191 q = 1) (hb : d135431 q = 1) : d138606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d138606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1191, d138606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1192 q = 1) (hb : d135431 q = 1) : d138607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1192, d138607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1192, d138607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24243 (p : Pattern) (ha : d1195 p = 1) (hb : d135431 p = 1) : d138610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24227 q ha hb
    | true =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d135431 q = 1) : d138574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d138574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d135431 q = 1) : d138608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d138608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d138608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d135431 q = 1) : d138609 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d138609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d138609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d135431 q = 1) : d138610 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, d138610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, d138610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24244 (p : Pattern) (ha : d1221 p = 1) (hb : d135431 p = 1) : d138619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1215 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1216 q = 1) (hb : d135431 q = 1) : d138614 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, d135431, d138614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1216, d135431, d138614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12559 q ha hb
  have h3 (q : Pattern) (ha : d1217 q = 1) (hb : d135431 q = 1) : d138615 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, d138615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1217, d138615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1218 q = 1) (hb : d135431 q = 1) : d138616 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, d138616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1218, d138616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1126 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1129 q = 1) (hb : d135431 q = 1) : d138554 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d135431, d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1129, d135431, d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
  have h7 (q : Pattern) (ha : d1130 q = 1) (hb : d135431 q = 1) : d138555 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1131 q = 1) (hb : d135431 q = 1) : d138556 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1219 q = 1) (hb : d135431 q = 1) : d138617 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1219, d138617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1219, d138617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1142 q = 1) (hb : d135431 q = 1) : d138557 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d135431, d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d1142, d135431, d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12537 q ha hb
  have h12 (q : Pattern) (ha : d1143 q = 1) (hb : d135431 q = 1) : d138558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1144 q = 1) (hb : d135431 q = 1) : d138559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1145 q = 1) (hb : d135431 q = 1) : d138560 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d138560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1145, d138560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1220 q = 1) (hb : d135431 q = 1) : d138618 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1220, d138618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1220, d138618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1221 q = 1) (hb : d135431 q = 1) : d138619 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1221, d138619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1221, d138619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro24245 (p : Pattern) (ha : d1227 p = 1) (hb : d135431 p = 1) : d138625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1222 q = 1) (hb : d135431 q = 1) : d138620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d138620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24244 q ha hb
    | true =>
      simp only [d1222, d138620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1223 q = 1) (hb : d135431 q = 1) : d138621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d138621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1223, d138621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1149 q = 1) (hb : d135431 q = 1) : d138564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24226 q ha hb
    | true =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1150 q = 1) (hb : d135431 q = 1) : d138565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1224 q = 1) (hb : d135431 q = 1) : d138622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1224, d138622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1224, d138622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1225 q = 1) (hb : d135431 q = 1) : d138623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1225, d138623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1225, d138623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1226 q = 1) (hb : d135431 q = 1) : d138624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1226, d138624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1226, d138624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1227 q = 1) (hb : d135431 q = 1) : d138625 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1227, d138625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1227, d138625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24246 (p : Pattern) (ha : d5552 p = 1) (hb : d135431 p = 1) : d138633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1129 q = 1) (hb : d135431 q = 1) : d138554 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d135431, d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1129, d135431, d138554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
  have h3 (q : Pattern) (ha : d1130 q = 1) (hb : d135431 q = 1) : d138555 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d138555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1131 q = 1) (hb : d135431 q = 1) : d138556 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d138556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1142 q = 1) (hb : d135431 q = 1) : d138557 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d135431, d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1142, d135431, d138557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12537 q ha hb
  have h7 (q : Pattern) (ha : d1143 q = 1) (hb : d135431 q = 1) : d138558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d138558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1144 q = 1) (hb : d135431 q = 1) : d138559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d138559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1145 q = 1) (hb : d135431 q = 1) : d138560 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d138560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1145, d138560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5545 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5546 q = 1) (hb : d94753 q = 1) : d5546 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d5547 q = 1) (hb : d135431 q = 1) : d138628 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5547, d135431, d138628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d5547, d135431, d138628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5548 q = 1) (hb : d135431 q = 1) : d138629 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5548, d138629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5548, d138629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5549 q = 1) (hb : d135431 q = 1) : d138630 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5549, d138630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5549, d138630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d5550 q = 1) (hb : d135431 q = 1) : d138631 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5550, d138631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5550, d138631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5551 q = 1) (hb : d135431 q = 1) : d138632 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5551, d138632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5551, d138632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5552 q = 1) (hb : d135431 q = 1) : d138633 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5552, d138633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5552, d138633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro24247 (p : Pattern) (ha : d5558 p = 1) (hb : d135431 p = 1) : d138639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5553 q = 1) (hb : d135431 q = 1) : d138634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5553, d138634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24246 q ha hb
    | true =>
      simp only [d5553, d138634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5554 q = 1) (hb : d135431 q = 1) : d138635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5554, d138635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5554, d138635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5555 q = 1) (hb : d135431 q = 1) : d138636 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5555, d138636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5555, d138636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5556 q = 1) (hb : d135431 q = 1) : d138637 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5556, d138637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5556, d138637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5557 q = 1) (hb : d135431 q = 1) : d138638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5557, d138638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5557, d138638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5558 q = 1) (hb : d135431 q = 1) : d138639 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5558, d138639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5558, d138639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24248 (p : Pattern) (ha : d74690 p = 1) (hb : d135431 p = 1) : d138645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d135431 q = 1) : d138601 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d138601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24240 q ha hb
    | true =>
      simp only [d1186, d138601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24241 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d135431 q = 1) : d138602 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d138602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d138602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d135431 q = 1) : d138603 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d138603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, d138603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d135431 q = 1) : d138604 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d138604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d138604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d135431 q = 1) : d138611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d138611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24242 q ha hb
    | true =>
      simp only [d1196, d138611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24243 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d135431 q = 1) : d138612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d138612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d138612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d135431 q = 1) : d138613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d138613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, d138613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1228 q = 1) (hb : d135431 q = 1) : d138626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d138626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24245 q ha hb
    | true =>
      simp only [d1228, d138626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24228 q ha hb
  have h9 (q : Pattern) (ha : d4485 q = 1) (hb : d135431 q = 1) : d138627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d138627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4485, d138627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5559 q = 1) (hb : d135431 q = 1) : d138640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5559, d138640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24247 q ha hb
    | true =>
      simp only [d5559, d138640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5560 q = 1) (hb : d135431 q = 1) : d138641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5560, d138641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5560, d138641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74687 q = 1) (hb : d135431 q = 1) : d138642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74687, d138642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74687, d138642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74688 q = 1) (hb : d135431 q = 1) : d138643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74688, d138643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74688, d138643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74689 q = 1) (hb : d135431 q = 1) : d138644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74689, d138644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74689, d138644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74690 q = 1) (hb : d135431 q = 1) : d138645 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74690, d138645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74690, d138645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24249 (p : Pattern) (ha : d1326 p = 1) (hb : d135431 p = 1) : d138646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d135431 q = 1) : d138564 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24226 q ha hb
    | true =>
      simp only [d1149, d138564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d135431 q = 1) : d138565 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d138565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d135431 q = 1) : d138568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24227 q ha hb
    | true =>
      simp only [d1153, d138568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d135431 q = 1) : d138569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d138569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d135431 q = 1) : d138570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d138570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d135431 q = 1) : d138571 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d138571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1182 q = 1) (hb : d135431 q = 1) : d138597 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d138597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d138597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1326 q = 1) (hb : d135431 q = 1) : d138646 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1326, d138646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1326, d138646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
