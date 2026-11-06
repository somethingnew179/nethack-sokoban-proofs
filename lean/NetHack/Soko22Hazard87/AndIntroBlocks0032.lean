import NetHack.Soko22Hazard87.AndIntroBlocks0031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro8000 (p : Pattern) (ha : d76439 p = 1) (hb : d77620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76434 q = 1) (hb : d77615 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d76434, d77615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7999 q ha hb
    | true =>
      simp only [d76434, d77615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76435 q = 1) (hb : d77616 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d76435, d77616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76435, d77616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76436 q = 1) (hb : d77617 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d76436, d77617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76436, d77617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76437 q = 1) (hb : d77618 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d76437, d77618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76437, d77618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76438 q = 1) (hb : d77619 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d76438, d77619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76438, d77619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76439 q = 1) (hb : d77620 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d76439, d77620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76439, d77620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8001 (p : Pattern) (ha : d76445 p = 1) (hb : d77626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76440 q = 1) (hb : d77621 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d76440, d77621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8000 q ha hb
    | true =>
      simp only [d76440, d77621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76441 q = 1) (hb : d77622 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d76441, d77622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76441, d77622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76442 q = 1) (hb : d77623 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d76442, d77623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76442, d77623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76443 q = 1) (hb : d77624 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d76443, d77624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76443, d77624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76444 q = 1) (hb : d77625 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d76444, d77625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76444, d77625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76445 q = 1) (hb : d77626 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d76445, d77626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76445, d77626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8002 (p : Pattern) (ha : d76451 p = 1) (hb : d77632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76446 q = 1) (hb : d77627 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d76446, d77627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8001 q ha hb
    | true =>
      simp only [d76446, d77627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76447 q = 1) (hb : d77628 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d76447, d77628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76447, d77628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76448 q = 1) (hb : d77629 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d76448, d77629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76448, d77629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76449 q = 1) (hb : d77630 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d76449, d77630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76449, d77630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76450 q = 1) (hb : d77631 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d76450, d77631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76450, d77631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76451 q = 1) (hb : d77632 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d76451, d77632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76451, d77632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8003 (p : Pattern) (ha : d69762 p = 1) (hb : d75629 p = 1) : d77635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d390 q = 1) (hb : d75629 q = 1) : d5356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4465 q ha hb
    | true =>
      simp only [d390, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4696 q = 1) (hb : d75629 q = 1) : d77258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4696, d77258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4696, d77258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4697 q = 1) (hb : d75629 q = 1) : d77259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4697, d77259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4697, d77259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4698 q = 1) (hb : d75629 q = 1) : d77260 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4698, d77260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4698, d77260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4699 q = 1) (hb : d75629 q = 1) : d77261 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4699, d77261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4699, d77261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69762 q = 1) (hb : d75629 q = 1) : d77635 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69762, d77635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69762, d77635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8004 (p : Pattern) (ha : d69772 p = 1) (hb : d75629 p = 1) : d77645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d451 q = 1) (hb : d75629 q = 1) : d5378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d451, d75629, d5378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4467 q ha hb
    | true =>
      simp only [d451, d75629, d5378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69768 q = 1) (hb : d75629 q = 1) : d77641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69768, d77641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69768, d77641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69769 q = 1) (hb : d75629 q = 1) : d77642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69769, d77642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69769, d77642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69770 q = 1) (hb : d75629 q = 1) : d77643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69770, d77643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69770, d77643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69771 q = 1) (hb : d75629 q = 1) : d77644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69771, d77644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69771, d77644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69772 q = 1) (hb : d75629 q = 1) : d77645 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69772, d77645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69772, d77645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8005 (p : Pattern) (ha : d69778 p = 1) (hb : d75629 p = 1) : d77651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4701 q = 1) (hb : d75629 q = 1) : d77263 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4701, d77263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7823 q ha hb
    | true =>
      simp only [d4701, d77263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7824 q ha hb
  have h2 (q : Pattern) (ha : d4702 q = 1) (hb : d75629 q = 1) : d77264 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4702, d77264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4702, d77264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69760 q = 1) (hb : d75629 q = 1) : d77633 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69760, d77633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69760, d77633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69761 q = 1) (hb : d75629 q = 1) : d77634 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69761, d77634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69761, d77634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69763 q = 1) (hb : d75629 q = 1) : d77636 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69763, d77636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69763, d77636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8003 q ha hb
  have h6 (q : Pattern) (ha : d69764 q = 1) (hb : d75629 q = 1) : d77637 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69764, d77637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69764, d77637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69765 q = 1) (hb : d75629 q = 1) : d77638 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69765, d77638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69765, d77638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69766 q = 1) (hb : d75629 q = 1) : d77639 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69766, d77639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69766, d77639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69767 q = 1) (hb : d75629 q = 1) : d77640 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69767, d77640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69767, d77640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69773 q = 1) (hb : d75629 q = 1) : d77646 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69773, d77646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69773, d77646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8004 q ha hb
  have h11 (q : Pattern) (ha : d69774 q = 1) (hb : d75629 q = 1) : d77647 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69774, d77647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69774, d77647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69775 q = 1) (hb : d75629 q = 1) : d77648 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69775, d77648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69775, d77648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69776 q = 1) (hb : d75629 q = 1) : d77649 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69776, d77649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69776, d77649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69777 q = 1) (hb : d75629 q = 1) : d77650 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69777, d77650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69777, d77650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69778 q = 1) (hb : d75629 q = 1) : d77651 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69778, d77651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69778, d77651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8006 (p : Pattern) (ha : d69784 p = 1) (hb : d75629 p = 1) : d77657 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d75629 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69779 q = 1) (hb : d75629 q = 1) : d77652 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69779, d77652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69779, d77652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8005 q ha hb
  have h3 (q : Pattern) (ha : d69780 q = 1) (hb : d75629 q = 1) : d77653 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69780, d77653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69780, d77653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69781 q = 1) (hb : d75629 q = 1) : d77654 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69781, d77654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69781, d77654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69782 q = 1) (hb : d75629 q = 1) : d77655 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69782, d77655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69782, d77655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69783 q = 1) (hb : d75629 q = 1) : d77656 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69783, d77656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69783, d77656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69784 q = 1) (hb : d75629 q = 1) : d77657 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69784, d77657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69784, d77657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8007 (p : Pattern) (ha : d69787 p = 1) (hb : d75629 p = 1) : d77660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d626 q = 1) (hb : d75629 q = 1) : d5407 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d75629, d5407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4476 q ha hb
    | true =>
      simp only [d626, d75629, d5407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4781 q = 1) (hb : d75629 q = 1) : d77312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4781, d77312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4781, d77312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4782 q = 1) (hb : d75629 q = 1) : d77313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4782, d77313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4782, d77313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4783 q = 1) (hb : d75629 q = 1) : d77314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4783, d77314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4783, d77314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4784 q = 1) (hb : d75629 q = 1) : d77315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4784, d77315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4784, d77315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69787 q = 1) (hb : d75629 q = 1) : d77660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69787, d77660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69787, d77660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8008 (p : Pattern) (ha : d69797 p = 1) (hb : d75629 p = 1) : d77670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d720 q = 1) (hb : d75629 q = 1) : d5429 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d720, d75629, d5429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4478 q ha hb
    | true =>
      simp only [d720, d75629, d5429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69793 q = 1) (hb : d75629 q = 1) : d77666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69793, d77666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69793, d77666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69794 q = 1) (hb : d75629 q = 1) : d77667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69794, d77667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69794, d77667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69795 q = 1) (hb : d75629 q = 1) : d77668 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69795, d77668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69795, d77668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69796 q = 1) (hb : d75629 q = 1) : d77669 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69796, d77669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69796, d77669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69797 q = 1) (hb : d75629 q = 1) : d77670 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69797, d77670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69797, d77670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8009 (p : Pattern) (ha : d69803 p = 1) (hb : d75629 p = 1) : d77676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4786 q = 1) (hb : d75629 q = 1) : d77317 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4786, d77317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7835 q ha hb
    | true =>
      simp only [d4786, d77317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7836 q ha hb
  have h2 (q : Pattern) (ha : d4787 q = 1) (hb : d75629 q = 1) : d77318 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4787, d77318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4787, d77318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69785 q = 1) (hb : d75629 q = 1) : d77658 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69785, d77658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69785, d77658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69786 q = 1) (hb : d75629 q = 1) : d77659 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69786, d77659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69786, d77659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69788 q = 1) (hb : d75629 q = 1) : d77661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69788, d77661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69788, d77661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8007 q ha hb
  have h6 (q : Pattern) (ha : d69789 q = 1) (hb : d75629 q = 1) : d77662 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69789, d77662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69789, d77662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69790 q = 1) (hb : d75629 q = 1) : d77663 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69790, d77663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69790, d77663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69791 q = 1) (hb : d75629 q = 1) : d77664 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69791, d77664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69791, d77664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69792 q = 1) (hb : d75629 q = 1) : d77665 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69792, d77665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69792, d77665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69798 q = 1) (hb : d75629 q = 1) : d77671 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69798, d77671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69798, d77671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8008 q ha hb
  have h11 (q : Pattern) (ha : d69799 q = 1) (hb : d75629 q = 1) : d77672 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69799, d77672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69799, d77672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69800 q = 1) (hb : d75629 q = 1) : d77673 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69800, d77673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69800, d77673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69801 q = 1) (hb : d75629 q = 1) : d77674 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69801, d77674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69801, d77674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69802 q = 1) (hb : d75629 q = 1) : d77675 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69802, d77675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69802, d77675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69803 q = 1) (hb : d75629 q = 1) : d77676 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69803, d77676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69803, d77676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8010 (p : Pattern) (ha : d69809 p = 1) (hb : d75629 p = 1) : d77682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69804 q = 1) (hb : d75629 q = 1) : d77677 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69804, d77677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69804, d77677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8009 q ha hb
  have h2 (q : Pattern) (ha : d69805 q = 1) (hb : d75629 q = 1) : d77678 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69805, d77678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69805, d77678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69806 q = 1) (hb : d75629 q = 1) : d77679 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69806, d77679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69806, d77679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69807 q = 1) (hb : d75629 q = 1) : d77680 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69807, d77680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69807, d77680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69808 q = 1) (hb : d75629 q = 1) : d77681 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69808, d77681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69808, d77681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69809 q = 1) (hb : d75629 q = 1) : d77682 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69809, d77682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69809, d77682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8011 (p : Pattern) (ha : d69813 p = 1) (hb : d75629 p = 1) : d77686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d932 q = 1) (hb : d75629 q = 1) : d6181 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d75629, d6181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4487 q ha hb
    | true =>
      simp only [d932, d75629, d6181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4876 q = 1) (hb : d75629 q = 1) : d77367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4876, d77367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4876, d77367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4877 q = 1) (hb : d75629 q = 1) : d77368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4877, d77368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4877, d77368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4878 q = 1) (hb : d75629 q = 1) : d77369 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4878, d77369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4878, d77369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4879 q = 1) (hb : d75629 q = 1) : d77370 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4879, d77370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4879, d77370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69813 q = 1) (hb : d75629 q = 1) : d77686 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69813, d77686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69813, d77686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8012 (p : Pattern) (ha : d69823 p = 1) (hb : d75629 p = 1) : d77696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1053 q = 1) (hb : d75629 q = 1) : d6234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1053, d75629, d6234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4489 q ha hb
    | true =>
      simp only [d1053, d75629, d6234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69819 q = 1) (hb : d75629 q = 1) : d77692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69819, d77692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69819, d77692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69820 q = 1) (hb : d75629 q = 1) : d77693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69820, d77693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69820, d77693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69821 q = 1) (hb : d75629 q = 1) : d77694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69821, d77694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69821, d77694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69822 q = 1) (hb : d75629 q = 1) : d77695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69822, d77695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69822, d77695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69823 q = 1) (hb : d75629 q = 1) : d77696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69823, d77696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69823, d77696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8013 (p : Pattern) (ha : d69829 p = 1) (hb : d75629 p = 1) : d77702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4881 q = 1) (hb : d75629 q = 1) : d77372 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4881, d77372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7847 q ha hb
    | true =>
      simp only [d4881, d77372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7848 q ha hb
  have h2 (q : Pattern) (ha : d4882 q = 1) (hb : d75629 q = 1) : d77373 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4882, d77373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4882, d77373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69811 q = 1) (hb : d75629 q = 1) : d77684 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69811, d77684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69811, d77684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69812 q = 1) (hb : d75629 q = 1) : d77685 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69812, d77685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69812, d77685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69814 q = 1) (hb : d75629 q = 1) : d77687 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69814, d77687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69814, d77687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8011 q ha hb
  have h6 (q : Pattern) (ha : d69815 q = 1) (hb : d75629 q = 1) : d77688 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69815, d77688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69815, d77688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69816 q = 1) (hb : d75629 q = 1) : d77689 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69816, d77689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69816, d77689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69817 q = 1) (hb : d75629 q = 1) : d77690 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69817, d77690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69817, d77690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69818 q = 1) (hb : d75629 q = 1) : d77691 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69818, d77691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69818, d77691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69824 q = 1) (hb : d75629 q = 1) : d77697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69824, d77697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69824, d77697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8012 q ha hb
  have h11 (q : Pattern) (ha : d69825 q = 1) (hb : d75629 q = 1) : d77698 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69825, d77698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69825, d77698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69826 q = 1) (hb : d75629 q = 1) : d77699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69826, d77699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69826, d77699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69827 q = 1) (hb : d75629 q = 1) : d77700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69827, d77700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69827, d77700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69828 q = 1) (hb : d75629 q = 1) : d77701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69828, d77701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69828, d77701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69829 q = 1) (hb : d75629 q = 1) : d77702 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69829, d77702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69829, d77702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8014 (p : Pattern) (ha : d69835 p = 1) (hb : d75629 p = 1) : d77708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69830 q = 1) (hb : d75629 q = 1) : d77703 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69830, d77703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69830, d77703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8013 q ha hb
  have h2 (q : Pattern) (ha : d69831 q = 1) (hb : d75629 q = 1) : d77704 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69831, d77704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69831, d77704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69832 q = 1) (hb : d75629 q = 1) : d77705 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69832, d77705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69832, d77705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69833 q = 1) (hb : d75629 q = 1) : d77706 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69833, d77706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69833, d77706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69834 q = 1) (hb : d75629 q = 1) : d77707 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69834, d77707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69834, d77707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69835 q = 1) (hb : d75629 q = 1) : d77708 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69835, d77708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69835, d77708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8015 (p : Pattern) (ha : d69840 p = 1) (hb : d75629 p = 1) : d77713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1343 q = 1) (hb : d75629 q = 1) : d6320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d75629, d6320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4498 q ha hb
    | true =>
      simp only [d1343, d75629, d6320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4972 q = 1) (hb : d75629 q = 1) : d77423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4972, d77423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4972, d77423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4973 q = 1) (hb : d75629 q = 1) : d77424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4973, d77424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4973, d77424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4974 q = 1) (hb : d75629 q = 1) : d77425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4974, d77425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4974, d77425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4975 q = 1) (hb : d75629 q = 1) : d77426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4975, d77426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4975, d77426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69840 q = 1) (hb : d75629 q = 1) : d77713 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69840, d77713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69840, d77713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8016 (p : Pattern) (ha : d69850 p = 1) (hb : d75629 p = 1) : d77723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1487 q = 1) (hb : d75629 q = 1) : d6379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1487, d75629, d6379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4500 q ha hb
    | true =>
      simp only [d1487, d75629, d6379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69846 q = 1) (hb : d75629 q = 1) : d77719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69846, d77719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69846, d77719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69847 q = 1) (hb : d75629 q = 1) : d77720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69847, d77720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69847, d77720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69848 q = 1) (hb : d75629 q = 1) : d77721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69848, d77721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69848, d77721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69849 q = 1) (hb : d75629 q = 1) : d77722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69849, d77722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69849, d77722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69850 q = 1) (hb : d75629 q = 1) : d77723 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69850, d77723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69850, d77723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8017 (p : Pattern) (ha : d69856 p = 1) (hb : d75629 p = 1) : d77729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4977 q = 1) (hb : d75629 q = 1) : d77428 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4977, d77428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7859 q ha hb
    | true =>
      simp only [d4977, d77428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7860 q ha hb
  have h2 (q : Pattern) (ha : d4978 q = 1) (hb : d75629 q = 1) : d77429 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4978, d77429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4978, d77429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69838 q = 1) (hb : d75629 q = 1) : d77711 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69838, d77711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69838, d77711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69839 q = 1) (hb : d75629 q = 1) : d77712 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69839, d77712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69839, d77712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69841 q = 1) (hb : d75629 q = 1) : d77714 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69841, d77714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69841, d77714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8015 q ha hb
  have h6 (q : Pattern) (ha : d69842 q = 1) (hb : d75629 q = 1) : d77715 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69842, d77715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69842, d77715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69843 q = 1) (hb : d75629 q = 1) : d77716 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69843, d77716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69843, d77716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69844 q = 1) (hb : d75629 q = 1) : d77717 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69844, d77717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69844, d77717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69845 q = 1) (hb : d75629 q = 1) : d77718 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69845, d77718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69845, d77718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69851 q = 1) (hb : d75629 q = 1) : d77724 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69851, d77724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69851, d77724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8016 q ha hb
  have h11 (q : Pattern) (ha : d69852 q = 1) (hb : d75629 q = 1) : d77725 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69852, d77725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69852, d77725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69853 q = 1) (hb : d75629 q = 1) : d77726 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69853, d77726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69853, d77726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69854 q = 1) (hb : d75629 q = 1) : d77727 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69854, d77727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69854, d77727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69855 q = 1) (hb : d75629 q = 1) : d77728 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69855, d77728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69855, d77728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69856 q = 1) (hb : d75629 q = 1) : d77729 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69856, d77729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69856, d77729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8018 (p : Pattern) (ha : d69862 p = 1) (hb : d75629 p = 1) : d77735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69857 q = 1) (hb : d75629 q = 1) : d77730 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69857, d77730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69857, d77730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8017 q ha hb
  have h2 (q : Pattern) (ha : d69858 q = 1) (hb : d75629 q = 1) : d77731 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69858, d77731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69858, d77731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69859 q = 1) (hb : d75629 q = 1) : d77732 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69859, d77732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69859, d77732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69860 q = 1) (hb : d75629 q = 1) : d77733 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69860, d77733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69860, d77733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69861 q = 1) (hb : d75629 q = 1) : d77734 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69861, d77734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69861, d77734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69862 q = 1) (hb : d75629 q = 1) : d77735 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69862, d77735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69862, d77735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8019 (p : Pattern) (ha : d69868 p = 1) (hb : d75629 p = 1) : d77741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1820 q = 1) (hb : d75629 q = 1) : d6466 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d75629, d6466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4509 q ha hb
    | true =>
      simp only [d1820, d75629, d6466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5083 q = 1) (hb : d75629 q = 1) : d77480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5083, d77480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5083, d77480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5084 q = 1) (hb : d75629 q = 1) : d77481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5084, d77481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5084, d77481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5085 q = 1) (hb : d75629 q = 1) : d77482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5085, d77482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5085, d77482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5086 q = 1) (hb : d75629 q = 1) : d77483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5086, d77483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5086, d77483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69868 q = 1) (hb : d75629 q = 1) : d77741 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69868, d77741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69868, d77741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8020 (p : Pattern) (ha : d69878 p = 1) (hb : d75629 p = 1) : d77751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1964 q = 1) (hb : d75629 q = 1) : d6525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1964, d75629, d6525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4511 q ha hb
    | true =>
      simp only [d1964, d75629, d6525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69874 q = 1) (hb : d75629 q = 1) : d77747 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69874, d77747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69874, d77747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69875 q = 1) (hb : d75629 q = 1) : d77748 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69875, d77748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69875, d77748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69876 q = 1) (hb : d75629 q = 1) : d77749 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69876, d77749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69876, d77749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69877 q = 1) (hb : d75629 q = 1) : d77750 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69877, d77750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69877, d77750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69878 q = 1) (hb : d75629 q = 1) : d77751 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69878, d77751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69878, d77751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8021 (p : Pattern) (ha : d69884 p = 1) (hb : d75629 p = 1) : d77757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5088 q = 1) (hb : d75629 q = 1) : d77485 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5088, d77485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7871 q ha hb
    | true =>
      simp only [d5088, d77485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7872 q ha hb
  have h2 (q : Pattern) (ha : d5089 q = 1) (hb : d75629 q = 1) : d77486 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5089, d77486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5089, d77486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69866 q = 1) (hb : d75629 q = 1) : d77739 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69866, d77739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69866, d77739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69867 q = 1) (hb : d75629 q = 1) : d77740 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69867, d77740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69867, d77740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69869 q = 1) (hb : d75629 q = 1) : d77742 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69869, d77742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69869, d77742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8019 q ha hb
  have h6 (q : Pattern) (ha : d69870 q = 1) (hb : d75629 q = 1) : d77743 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69870, d77743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69870, d77743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69871 q = 1) (hb : d75629 q = 1) : d77744 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69871, d77744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69871, d77744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69872 q = 1) (hb : d75629 q = 1) : d77745 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69872, d77745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69872, d77745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69873 q = 1) (hb : d75629 q = 1) : d77746 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69873, d77746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69873, d77746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69879 q = 1) (hb : d75629 q = 1) : d77752 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69879, d77752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69879, d77752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8020 q ha hb
  have h11 (q : Pattern) (ha : d69880 q = 1) (hb : d75629 q = 1) : d77753 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69880, d77753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69880, d77753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69881 q = 1) (hb : d75629 q = 1) : d77754 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69881, d77754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69881, d77754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69882 q = 1) (hb : d75629 q = 1) : d77755 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69882, d77755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69882, d77755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69883 q = 1) (hb : d75629 q = 1) : d77756 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69883, d77756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69883, d77756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69884 q = 1) (hb : d75629 q = 1) : d77757 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69884, d77757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69884, d77757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8022 (p : Pattern) (ha : d69890 p = 1) (hb : d75629 p = 1) : d77763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69885 q = 1) (hb : d75629 q = 1) : d77758 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69885, d77758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69885, d77758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8021 q ha hb
  have h2 (q : Pattern) (ha : d69886 q = 1) (hb : d75629 q = 1) : d77759 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69886, d77759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69886, d77759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69887 q = 1) (hb : d75629 q = 1) : d77760 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69887, d77760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69887, d77760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69888 q = 1) (hb : d75629 q = 1) : d77761 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69888, d77761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69888, d77761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69889 q = 1) (hb : d75629 q = 1) : d77762 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69889, d77762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69889, d77762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69890 q = 1) (hb : d75629 q = 1) : d77763 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69890, d77763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69890, d77763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8023 (p : Pattern) (ha : d69897 p = 1) (hb : d75629 p = 1) : d77770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2298 q = 1) (hb : d75629 q = 1) : d6613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d75629, d6613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4520 q ha hb
    | true =>
      simp only [d2298, d75629, d6613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5200 q = 1) (hb : d75629 q = 1) : d77538 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5200, d77538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5200, d77538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5201 q = 1) (hb : d75629 q = 1) : d77539 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5201, d77539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5201, d77539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5202 q = 1) (hb : d75629 q = 1) : d77540 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5202, d77540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5202, d77540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5203 q = 1) (hb : d75629 q = 1) : d77541 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5203, d77541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5203, d77541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69897 q = 1) (hb : d75629 q = 1) : d77770 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69897, d77770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69897, d77770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8024 (p : Pattern) (ha : d69907 p = 1) (hb : d75629 p = 1) : d77780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2442 q = 1) (hb : d75629 q = 1) : d6672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2442, d75629, d6672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4522 q ha hb
    | true =>
      simp only [d2442, d75629, d6672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69903 q = 1) (hb : d75629 q = 1) : d77776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69903, d77776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69903, d77776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69904 q = 1) (hb : d75629 q = 1) : d77777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69904, d77777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69904, d77777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69905 q = 1) (hb : d75629 q = 1) : d77778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69905, d77778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69905, d77778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69906 q = 1) (hb : d75629 q = 1) : d77779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69906, d77779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69906, d77779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69907 q = 1) (hb : d75629 q = 1) : d77780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69907, d77780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69907, d77780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8025 (p : Pattern) (ha : d69913 p = 1) (hb : d75629 p = 1) : d77786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5205 q = 1) (hb : d75629 q = 1) : d77543 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5205, d77543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7883 q ha hb
    | true =>
      simp only [d5205, d77543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7884 q ha hb
  have h2 (q : Pattern) (ha : d5206 q = 1) (hb : d75629 q = 1) : d77544 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5206, d77544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5206, d77544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69895 q = 1) (hb : d75629 q = 1) : d77768 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69895, d77768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69895, d77768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69896 q = 1) (hb : d75629 q = 1) : d77769 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69896, d77769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69896, d77769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69898 q = 1) (hb : d75629 q = 1) : d77771 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69898, d77771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69898, d77771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8023 q ha hb
  have h6 (q : Pattern) (ha : d69899 q = 1) (hb : d75629 q = 1) : d77772 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69899, d77772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69899, d77772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69900 q = 1) (hb : d75629 q = 1) : d77773 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69900, d77773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69900, d77773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69901 q = 1) (hb : d75629 q = 1) : d77774 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69901, d77774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69901, d77774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69902 q = 1) (hb : d75629 q = 1) : d77775 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69902, d77775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69902, d77775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69908 q = 1) (hb : d75629 q = 1) : d77781 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69908, d77781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69908, d77781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8024 q ha hb
  have h11 (q : Pattern) (ha : d69909 q = 1) (hb : d75629 q = 1) : d77782 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69909, d77782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69909, d77782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69910 q = 1) (hb : d75629 q = 1) : d77783 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69910, d77783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69910, d77783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69911 q = 1) (hb : d75629 q = 1) : d77784 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69911, d77784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69911, d77784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69912 q = 1) (hb : d75629 q = 1) : d77785 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69912, d77785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69912, d77785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69913 q = 1) (hb : d75629 q = 1) : d77786 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69913, d77786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69913, d77786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8026 (p : Pattern) (ha : d69919 p = 1) (hb : d75629 p = 1) : d77792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69914 q = 1) (hb : d75629 q = 1) : d77787 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69914, d77787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69914, d77787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8025 q ha hb
  have h2 (q : Pattern) (ha : d69915 q = 1) (hb : d75629 q = 1) : d77788 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69915, d77788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69915, d77788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69916 q = 1) (hb : d75629 q = 1) : d77789 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69916, d77789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69916, d77789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69917 q = 1) (hb : d75629 q = 1) : d77790 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69917, d77790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69917, d77790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69918 q = 1) (hb : d75629 q = 1) : d77791 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69918, d77791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69918, d77791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69919 q = 1) (hb : d75629 q = 1) : d77792 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69919, d77792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69919, d77792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8027 (p : Pattern) (ha : d69925 p = 1) (hb : d75629 p = 1) : d77798 p = 1 := by
  have h0 (q : Pattern) (ha : d69810 q = 1) (hb : d75629 q = 1) : d77683 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69810, d77683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8006 q ha hb
    | true =>
      simp only [d69810, d77683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8010 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69836 q = 1) (hb : d75629 q = 1) : d77709 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69836, d77709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69836, d77709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8014 q ha hb
  have h3 (q : Pattern) (ha : d69837 q = 1) (hb : d75629 q = 1) : d77710 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69837, d77710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69837, d77710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69863 q = 1) (hb : d75629 q = 1) : d77736 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69863, d77736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69863, d77736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8018 q ha hb
  have h5 (q : Pattern) (ha : d69864 q = 1) (hb : d75629 q = 1) : d77737 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69864, d77737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69864, d77737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69865 q = 1) (hb : d75629 q = 1) : d77738 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69865, d77738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69865, d77738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69891 q = 1) (hb : d75629 q = 1) : d77764 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69891, d77764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69891, d77764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8022 q ha hb
  have h8 (q : Pattern) (ha : d69892 q = 1) (hb : d75629 q = 1) : d77765 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69892, d77765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69892, d77765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69893 q = 1) (hb : d75629 q = 1) : d77766 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69893, d77766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69893, d77766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69894 q = 1) (hb : d75629 q = 1) : d77767 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69894, d77767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69894, d77767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69920 q = 1) (hb : d75629 q = 1) : d77793 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69920, d77793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69920, d77793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8026 q ha hb
  have h12 (q : Pattern) (ha : d69921 q = 1) (hb : d75629 q = 1) : d77794 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69921, d77794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69921, d77794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69922 q = 1) (hb : d75629 q = 1) : d77795 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69922, d77795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69922, d77795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69923 q = 1) (hb : d75629 q = 1) : d77796 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69923, d77796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69923, d77796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69924 q = 1) (hb : d75629 q = 1) : d77797 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d69924, d77797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69924, d77797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69925 q = 1) (hb : d75629 q = 1) : d77798 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d69925, d77798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69925, d77798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro8028 (p : Pattern) (ha : d69931 p = 1) (hb : d75629 p = 1) : d77804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69926 q = 1) (hb : d75629 q = 1) : d77799 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d69926, d77799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8027 q ha hb
    | true =>
      simp only [d69926, d77799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69927 q = 1) (hb : d75629 q = 1) : d77800 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d69927, d77800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69927, d77800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69928 q = 1) (hb : d75629 q = 1) : d77801 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d69928, d77801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69928, d77801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69929 q = 1) (hb : d75629 q = 1) : d77802 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d69929, d77802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69929, d77802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69930 q = 1) (hb : d75629 q = 1) : d77803 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d69930, d77803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69930, d77803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69931 q = 1) (hb : d75629 q = 1) : d77804 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d69931, d77804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69931, d77804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8029 (p : Pattern) (ha : d69937 p = 1) (hb : d75629 p = 1) : d77810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69932 q = 1) (hb : d75629 q = 1) : d77805 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d69932, d77805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8028 q ha hb
    | true =>
      simp only [d69932, d77805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69933 q = 1) (hb : d75629 q = 1) : d77806 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d69933, d77806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69933, d77806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69934 q = 1) (hb : d75629 q = 1) : d77807 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d69934, d77807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69934, d77807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69935 q = 1) (hb : d75629 q = 1) : d77808 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d69935, d77808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69935, d77808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69936 q = 1) (hb : d75629 q = 1) : d77809 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d69936, d77809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69936, d77809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69937 q = 1) (hb : d75629 q = 1) : d77810 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d69937, d77810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69937, d77810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8030 (p : Pattern) (ha : d69943 p = 1) (hb : d75629 p = 1) : d77816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69938 q = 1) (hb : d75629 q = 1) : d77811 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d69938, d77811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8029 q ha hb
    | true =>
      simp only [d69938, d77811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69939 q = 1) (hb : d75629 q = 1) : d77812 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d69939, d77812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69939, d77812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69940 q = 1) (hb : d75629 q = 1) : d77813 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d69940, d77813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69940, d77813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69941 q = 1) (hb : d75629 q = 1) : d77814 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d69941, d77814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69941, d77814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69942 q = 1) (hb : d75629 q = 1) : d77815 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d69942, d77815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69942, d77815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69943 q = 1) (hb : d75629 q = 1) : d77816 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d69943, d77816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69943, d77816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8031 (p : Pattern) (ha : d69949 p = 1) (hb : d75629 p = 1) : d77822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69944 q = 1) (hb : d75629 q = 1) : d77817 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d69944, d77817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8030 q ha hb
    | true =>
      simp only [d69944, d77817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69945 q = 1) (hb : d75629 q = 1) : d77818 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d69945, d77818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69945, d77818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69946 q = 1) (hb : d75629 q = 1) : d77819 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d69946, d77819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69946, d77819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69947 q = 1) (hb : d75629 q = 1) : d77820 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d69947, d77820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69947, d77820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69948 q = 1) (hb : d75629 q = 1) : d77821 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d69948, d77821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69948, d77821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69949 q = 1) (hb : d75629 q = 1) : d77822 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d69949, d77822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69949, d77822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8032 (p : Pattern) (ha : d69955 p = 1) (hb : d75629 p = 1) : d77828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69950 q = 1) (hb : d75629 q = 1) : d77823 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d69950, d77823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8031 q ha hb
    | true =>
      simp only [d69950, d77823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69951 q = 1) (hb : d75629 q = 1) : d77824 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d69951, d77824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69951, d77824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69952 q = 1) (hb : d75629 q = 1) : d77825 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d69952, d77825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69952, d77825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69953 q = 1) (hb : d75629 q = 1) : d77826 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d69953, d77826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69953, d77826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69954 q = 1) (hb : d75629 q = 1) : d77827 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d69954, d77827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69954, d77827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69955 q = 1) (hb : d75629 q = 1) : d77828 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d69955, d77828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69955, d77828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8033 (p : Pattern) (ha : d69961 p = 1) (hb : d75629 p = 1) : d77834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69956 q = 1) (hb : d75629 q = 1) : d77829 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d69956, d77829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8032 q ha hb
    | true =>
      simp only [d69956, d77829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69957 q = 1) (hb : d75629 q = 1) : d77830 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d69957, d77830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69957, d77830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69958 q = 1) (hb : d75629 q = 1) : d77831 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d69958, d77831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69958, d77831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69959 q = 1) (hb : d75629 q = 1) : d77832 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d69959, d77832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69959, d77832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69960 q = 1) (hb : d75629 q = 1) : d77833 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d69960, d77833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69960, d77833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69961 q = 1) (hb : d75629 q = 1) : d77834 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d69961, d77834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69961, d77834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8034 (p : Pattern) (ha : d69967 p = 1) (hb : d75629 p = 1) : d77840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69962 q = 1) (hb : d75629 q = 1) : d77835 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d69962, d77835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8033 q ha hb
    | true =>
      simp only [d69962, d77835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69963 q = 1) (hb : d75629 q = 1) : d77836 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d69963, d77836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69963, d77836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69964 q = 1) (hb : d75629 q = 1) : d77837 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d69964, d77837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69964, d77837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69965 q = 1) (hb : d75629 q = 1) : d77838 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d69965, d77838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69965, d77838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69966 q = 1) (hb : d75629 q = 1) : d77839 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d69966, d77839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69966, d77839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69967 q = 1) (hb : d75629 q = 1) : d77840 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d69967, d77840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69967, d77840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8035 (p : Pattern) (ha : d104 p = 1) (hb : d75636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d75632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d75632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d75632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d75633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d75633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d75633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d75634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d75634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d75634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d75635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d75635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d75635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d75636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d75636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d75636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8036 (p : Pattern) (ha : d111 p = 1) (hb : d75642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d75632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d75632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d75632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d75633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d75633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d75633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d75634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d75634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d75634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d75635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d75635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d75635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d75637 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d107 q = 1) (hb : d75638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d75638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107, d75638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d108 q = 1) (hb : d75639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d75639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108, d75639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109 q = 1) (hb : d75640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d75640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109, d75640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d110 q = 1) (hb : d75641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d75641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d110, d75641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d111 q = 1) (hb : d75642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d75642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d111, d75642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8037 (p : Pattern) (ha : d406 p = 1) (hb : d75649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75637 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d75638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d75638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d75638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d75639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d75639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d75639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d75647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d75647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d75647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d75648 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d75648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d75648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d75649 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d75649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d75649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8038 (p : Pattern) (ha : d462 p = 1) (hb : d75660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75655 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d75656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d75656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d75656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d75657 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d75657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d75657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d75658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d75658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d75658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d75659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d75659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d75659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d75660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d75660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d75660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8039 (p : Pattern) (ha : d53647 p = 1) (hb : d75666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d75643 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d75643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8035 q ha hb
    | true =>
      simp only [d112, d75643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8036 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d75644 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d75644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d75644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d75645 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d75645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d75645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d75646 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d75646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d75646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d75650 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d75650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d75650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8037 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d75651 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d75651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d75651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d75652 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d75652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d75652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d75653 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d75653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d75653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d75654 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d75654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d75654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d75661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d75661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d75661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8038 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d75662 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d75662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d75662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d75663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d75663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d75663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d75664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d75664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d75664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d75665 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d75665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d75665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d75666 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d75666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d75666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8040 (p : Pattern) (ha : d75708 p = 1) (hb : d77255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75692 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75698 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d75703 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4737 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d4737, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4738 q = 1) (hb : d75704 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4738, d75704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4738, d75704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4739 q = 1) (hb : d75705 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4739, d75705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4739, d75705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4740 q = 1) (hb : d75706 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4740, d75706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4740, d75706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4741 q = 1) (hb : d75707 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4741, d75707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4741, d75707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75708 q = 1) (hb : d77255 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75708, d77255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75708, d77255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro8041 (p : Pattern) (ha : d75724 p = 1) (hb : d77262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75692 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75698 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75703 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4737 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d4737, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4738 q = 1) (hb : d75704 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4738, d75704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4738, d75704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4739 q = 1) (hb : d75705 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4739, d75705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4739, d75705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4740 q = 1) (hb : d75706 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4740, d75706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4740, d75706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4741 q = 1) (hb : d75707 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4741, d75707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4741, d75707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d75713 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d75717 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d75719 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d5356 q = 1) (hb : d75637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
    | true =>
      simp only [d5356, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75720 q = 1) (hb : d77258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75720, d77258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d75720, d77258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d75721 q = 1) (hb : d77259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75721, d77259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75721, d77259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d75722 q = 1) (hb : d77260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75722, d77260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75722, d77260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d75723 q = 1) (hb : d77261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75723, d77261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d75723, d77261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d75724 q = 1) (hb : d77262 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75724, d77262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d75724, d77262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro8042 (p : Pattern) (ha : d75733 p = 1) (hb : d77635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75719 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d75637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
    | true =>
      simp only [d5356, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75720 q = 1) (hb : d77258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75720, d77258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75720, d77258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d75721 q = 1) (hb : d77259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75721, d77259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75721, d77259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75731 q = 1) (hb : d77260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75731, d77260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75731, d77260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75732 q = 1) (hb : d77261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75732, d77261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75732, d77261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75733 q = 1) (hb : d77635 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75733, d77635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75733, d77635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8043 (p : Pattern) (ha : d75748 p = 1) (hb : d77645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75743 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51935 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d75655 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d75655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7498 q ha hb
    | true =>
      simp only [d5378, d75655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75744 q = 1) (hb : d77641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75744, d77641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75744, d77641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d75745 q = 1) (hb : d77642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75745, d77642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75745, d77642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75746 q = 1) (hb : d77643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75746, d77643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75746, d77643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75747 q = 1) (hb : d77644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75747, d77644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75747, d77644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75748 q = 1) (hb : d77645 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75748, d77645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75748, d77645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8044 (p : Pattern) (ha : d75754 p = 1) (hb : d77651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75725 q = 1) (hb : d77263 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75725, d77263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8040 q ha hb
    | true =>
      simp only [d75725, d77263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8041 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75728 q = 1) (hb : d77264 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75728, d77264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75728, d77264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75729 q = 1) (hb : d77633 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75729, d77633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75729, d77633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75730 q = 1) (hb : d77634 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75730, d77634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75730, d77634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75734 q = 1) (hb : d77636 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75734, d77636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75734, d77636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8042 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d75735 q = 1) (hb : d77637 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75735, d77637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75735, d77637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d75736 q = 1) (hb : d77638 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75736, d77638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d75736, d77638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d75737 q = 1) (hb : d77639 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75737, d77639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75737, d77639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d75738 q = 1) (hb : d77640 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75738, d77640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75738, d77640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d75749 q = 1) (hb : d77646 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75749, d77646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75749, d77646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8043 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75750 q = 1) (hb : d77647 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75750, d77647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75750, d77647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75751 q = 1) (hb : d77648 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75751, d77648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75751, d77648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d75752 q = 1) (hb : d77649 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75752, d77649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75752, d77649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d75753 q = 1) (hb : d77650 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75753, d77650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75753, d77650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d75754 q = 1) (hb : d77651 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75754, d77651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d75754, d77651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8045 (p : Pattern) (ha : d75760 p = 1) (hb : d77657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d75667 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d75667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d75667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8039 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d75668 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d75668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d75668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d75669 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d75669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d75669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d75670 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d75670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d75670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d75671 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d75671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d75671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75755 q = 1) (hb : d77652 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75755, d77652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75755, d77652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8044 q ha hb
  have h8 (q : Pattern) (ha : d75756 q = 1) (hb : d77653 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75756, d77653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75756, d77653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75757 q = 1) (hb : d77654 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75757, d77654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75757, d77654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75758 q = 1) (hb : d77655 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75758, d77655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75758, d77655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75759 q = 1) (hb : d77656 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75759, d77656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75759, d77656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d75760 q = 1) (hb : d77657 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d75760, d77657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d75760, d77657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8046 (p : Pattern) (ha : d75799 p = 1) (hb : d77309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75783 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d75794 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52238 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5400 q = 1) (hb : d75761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d75761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7510 q ha hb
    | true =>
      simp only [d5400, d75761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75795 q = 1) (hb : d77305 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75795, d77305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75795, d77305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d75796 q = 1) (hb : d77306 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75796, d77306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75796, d77306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75797 q = 1) (hb : d77307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75797, d77307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75797, d77307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75798 q = 1) (hb : d77308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75798, d77308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75798, d77308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75799 q = 1) (hb : d77309 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75799, d77309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75799, d77309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8047 (p : Pattern) (ha : d75816 p = 1) (hb : d77316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75783 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75789 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52238 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5400 q = 1) (hb : d75761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d75761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7510 q ha hb
    | true =>
      simp only [d5400, d75761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75795 q = 1) (hb : d77305 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75795, d77305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75795, d77305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75796 q = 1) (hb : d77306 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75796, d77306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75796, d77306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75797 q = 1) (hb : d77307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75797, d77307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75797, d77307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75798 q = 1) (hb : d77308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75798, d77308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75798, d77308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d75804 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d75808 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d75811 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52248 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d5407 q = 1) (hb : d75769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d75769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7513 q ha hb
    | true =>
      simp only [d5407, d75769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75812 q = 1) (hb : d77312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75812, d77312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d75812, d77312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d75813 q = 1) (hb : d77313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75813, d77313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75813, d77313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d75814 q = 1) (hb : d77314 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75814, d77314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75814, d77314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d75815 q = 1) (hb : d77315 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75815, d77315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d75815, d77315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d75816 q = 1) (hb : d77316 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75816, d77316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d75816, d77316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro8048 (p : Pattern) (ha : d75830 p = 1) (hb : d77660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52248 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5407 q = 1) (hb : d75769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d75769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7513 q ha hb
    | true =>
      simp only [d5407, d75769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75812 q = 1) (hb : d77312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75812, d77312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75812, d77312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d75813 q = 1) (hb : d77313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75813, d77313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75813, d77313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75828 q = 1) (hb : d77314 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75828, d77314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75828, d77314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75829 q = 1) (hb : d77315 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75829, d77315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75829, d77315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75830 q = 1) (hb : d77660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75830, d77660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75830, d77660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8049 (p : Pattern) (ha : d75859 p = 1) (hb : d77670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75853 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5429 q = 1) (hb : d75854 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5429, d75854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7517 q ha hb
    | true =>
      simp only [d5429, d75854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75855 q = 1) (hb : d77666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75855, d77666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75855, d77666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74156 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d75856 q = 1) (hb : d77667 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75856, d77667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75856, d77667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75857 q = 1) (hb : d77668 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75857, d77668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75857, d77668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75858 q = 1) (hb : d77669 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75858, d77669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75858, d77669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75859 q = 1) (hb : d77670 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75859, d77670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75859, d77670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8050 (p : Pattern) (ha : d75865 p = 1) (hb : d77676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75817 q = 1) (hb : d77317 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75817, d77317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8046 q ha hb
    | true =>
      simp only [d75817, d77317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8047 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75824 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75825 q = 1) (hb : d77318 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75825, d77318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75825, d77318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75826 q = 1) (hb : d77658 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75826, d77658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75826, d77658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75827 q = 1) (hb : d77659 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75827, d77659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75827, d77659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75831 q = 1) (hb : d77661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75831, d77661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75831, d77661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8048 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d75832 q = 1) (hb : d77662 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75832, d77662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75832, d77662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d75833 q = 1) (hb : d77663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75833, d77663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d75833, d77663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d75834 q = 1) (hb : d77664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75834, d77664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75834, d77664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d75835 q = 1) (hb : d77665 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75835, d77665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75835, d77665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d75860 q = 1) (hb : d77671 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75860, d77671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75860, d77671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8049 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75861 q = 1) (hb : d77672 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75861, d77672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75861, d77672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75862 q = 1) (hb : d77673 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75862, d77673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75862, d77673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d75863 q = 1) (hb : d77674 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75863, d77674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75863, d77674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d75864 q = 1) (hb : d77675 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75864, d77675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75864, d77675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d75865 q = 1) (hb : d77676 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75865, d77676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d75865, d77676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8051 (p : Pattern) (ha : d75871 p = 1) (hb : d77682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75866 q = 1) (hb : d77677 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75866, d77677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75866, d77677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8050 q ha hb
  have h2 (q : Pattern) (ha : d75867 q = 1) (hb : d77678 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75867, d77678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75867, d77678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75868 q = 1) (hb : d77679 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75868, d77679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75868, d77679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75869 q = 1) (hb : d77680 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75869, d77680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75869, d77680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75870 q = 1) (hb : d77681 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75870, d77681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75870, d77681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75871 q = 1) (hb : d77682 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d75871, d77682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75871, d77682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8052 (p : Pattern) (ha : d75918 p = 1) (hb : d77364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75900 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75906 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d75911 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52460 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6160 q = 1) (hb : d75877 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d75877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7522 q ha hb
    | true =>
      simp only [d6160, d75877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75912 q = 1) (hb : d77360 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75912, d77360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75912, d77360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d75915 q = 1) (hb : d77361 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75915, d77361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75915, d77361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75916 q = 1) (hb : d77362 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75916, d77362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75916, d77362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75917 q = 1) (hb : d77363 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75917, d77363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75917, d77363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75918 q = 1) (hb : d77364 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75918, d77364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75918, d77364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8053 (p : Pattern) (ha : d75937 p = 1) (hb : d77371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75900 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75906 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75911 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52460 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6160 q = 1) (hb : d75877 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d75877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7522 q ha hb
    | true =>
      simp only [d6160, d75877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75912 q = 1) (hb : d77360 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75912, d77360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75912, d77360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75915 q = 1) (hb : d77361 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75915, d77361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75915, d77361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75916 q = 1) (hb : d77362 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75916, d77362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75916, d77362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75917 q = 1) (hb : d77363 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75917, d77363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75917, d77363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d75923 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d75927 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d75930 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52470 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d6181 q = 1) (hb : d75886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d75886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7525 q ha hb
    | true =>
      simp only [d6181, d75886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75931 q = 1) (hb : d77367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75931, d77367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d75931, d77367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d75934 q = 1) (hb : d77368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75934, d77368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75934, d77368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d75935 q = 1) (hb : d77369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75935, d77369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75935, d77369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d75936 q = 1) (hb : d77370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75936, d77370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d75936, d77370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d75937 q = 1) (hb : d77371 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75937, d77371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d75937, d77371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro8054 (p : Pattern) (ha : d75951 p = 1) (hb : d77686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75930 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52470 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6181 q = 1) (hb : d75886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d75886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7525 q ha hb
    | true =>
      simp only [d6181, d75886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75931 q = 1) (hb : d77367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75931, d77367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75931, d77367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d75934 q = 1) (hb : d77368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75934, d77368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75934, d77368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75949 q = 1) (hb : d77369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75949, d77369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75949, d77369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75950 q = 1) (hb : d77370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75950, d77370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75950, d77370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75951 q = 1) (hb : d77686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75951, d77686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75951, d77686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8055 (p : Pattern) (ha : d75986 p = 1) (hb : d77696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52635 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6234 q = 1) (hb : d75979 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6234, d75979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7530 q ha hb
    | true =>
      simp only [d6234, d75979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75980 q = 1) (hb : d77692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75980, d77692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75980, d77692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d75982 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d75983 q = 1) (hb : d77693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75983, d77693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75983, d77693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75984 q = 1) (hb : d77694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75984, d77694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75984, d77694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75985 q = 1) (hb : d77695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75985, d77695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75985, d77695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75986 q = 1) (hb : d77696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75986, d77696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75986, d77696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8056 (p : Pattern) (ha : d75992 p = 1) (hb : d77702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75894 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75938 q = 1) (hb : d77372 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75938, d77372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8052 q ha hb
    | true =>
      simp only [d75938, d77372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8053 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75946 q = 1) (hb : d77373 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75946, d77373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75946, d77373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75947 q = 1) (hb : d77684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75947, d77684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75947, d77684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75948 q = 1) (hb : d77685 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75948, d77685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75948, d77685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75952 q = 1) (hb : d77687 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75952, d77687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75952, d77687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8054 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d75953 q = 1) (hb : d77688 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75953, d77688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75953, d77688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d75954 q = 1) (hb : d77689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75954, d77689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d75954, d77689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d75955 q = 1) (hb : d77690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75955, d77690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75955, d77690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d75956 q = 1) (hb : d77691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75956, d77691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75956, d77691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d75987 q = 1) (hb : d77697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75987, d77697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75987, d77697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8055 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75988 q = 1) (hb : d77698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75988, d77698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75988, d77698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75989 q = 1) (hb : d77699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75989, d77699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75989, d77699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d75990 q = 1) (hb : d77700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75990, d77700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75990, d77700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d75991 q = 1) (hb : d77701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75991, d77701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75991, d77701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d75992 q = 1) (hb : d77702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75992, d77702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d75992, d77702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8057 (p : Pattern) (ha : d75998 p = 1) (hb : d77708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75993 q = 1) (hb : d77703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75993, d77703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75993, d77703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8056 q ha hb
  have h2 (q : Pattern) (ha : d75994 q = 1) (hb : d77704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75994, d77704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75994, d77704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75995 q = 1) (hb : d77705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75995, d77705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75995, d77705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75996 q = 1) (hb : d77706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75996, d77706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75996, d77706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75997 q = 1) (hb : d77707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75997, d77707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75997, d77707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75998 q = 1) (hb : d77708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d75998, d77708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75998, d77708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8058 (p : Pattern) (ha : d76046 p = 1) (hb : d77420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76028 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76034 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d76039 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52743 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6299 q = 1) (hb : d76005 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d76005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7534 q ha hb
    | true =>
      simp only [d6299, d76005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76040 q = 1) (hb : d77416 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76040, d77416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76040, d77416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d76043 q = 1) (hb : d77417 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76043, d77417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76043, d77417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d76044 q = 1) (hb : d77418 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76044, d77418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76044, d77418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76045 q = 1) (hb : d77419 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76045, d77419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76045, d77419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76046 q = 1) (hb : d77420 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76046, d77420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76046, d77420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8059 (p : Pattern) (ha : d76065 p = 1) (hb : d77427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76028 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76039 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52743 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6299 q = 1) (hb : d76005 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d76005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7534 q ha hb
    | true =>
      simp only [d6299, d76005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76040 q = 1) (hb : d77416 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76040, d77416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76040, d77416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76043 q = 1) (hb : d77417 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76043, d77417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76043, d77417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76044 q = 1) (hb : d77418 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76044, d77418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76044, d77418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76045 q = 1) (hb : d77419 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76045, d77419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76045, d77419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d76051 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d76055 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d76058 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52753 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d6320 q = 1) (hb : d76014 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d76014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7537 q ha hb
    | true =>
      simp only [d6320, d76014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76059 q = 1) (hb : d77423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76059, d77423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d76059, d77423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d76062 q = 1) (hb : d77424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76062, d77424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76062, d77424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d76063 q = 1) (hb : d77425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76063, d77425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76063, d77425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d76064 q = 1) (hb : d77426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76064, d77426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76064, d77426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76065 q = 1) (hb : d77427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76065, d77427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76065, d77427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro8060 (p : Pattern) (ha : d76079 p = 1) (hb : d77713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76058 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52753 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6320 q = 1) (hb : d76014 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d76014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7537 q ha hb
    | true =>
      simp only [d6320, d76014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76059 q = 1) (hb : d77423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76059, d77423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76059, d77423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76062 q = 1) (hb : d77424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76062, d77424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76062, d77424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76077 q = 1) (hb : d77425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76077, d77425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76077, d77425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76078 q = 1) (hb : d77426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76078, d77426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76078, d77426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76079 q = 1) (hb : d77713 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76079, d77713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76079, d77713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8061 (p : Pattern) (ha : d76120 p = 1) (hb : d77723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76108 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52929 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6379 q = 1) (hb : d76113 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6379, d76113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7542 q ha hb
    | true =>
      simp only [d6379, d76113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76114 q = 1) (hb : d77719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76114, d77719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76114, d77719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76116 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76117 q = 1) (hb : d77720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76117, d77720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76117, d77720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76118 q = 1) (hb : d77721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76118, d77721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76118, d77721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76119 q = 1) (hb : d77722 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76119, d77722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76119, d77722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76120 q = 1) (hb : d77723 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76120, d77723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76120, d77723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8062 (p : Pattern) (ha : d76126 p = 1) (hb : d77729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76022 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76066 q = 1) (hb : d77428 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76066, d77428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8058 q ha hb
    | true =>
      simp only [d76066, d77428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8059 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76073 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76074 q = 1) (hb : d77429 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76074, d77429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76074, d77429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76075 q = 1) (hb : d77711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76075, d77711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76075, d77711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76076 q = 1) (hb : d77712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76076, d77712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76076, d77712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76080 q = 1) (hb : d77714 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76080, d77714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76080, d77714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8060 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76081 q = 1) (hb : d77715 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76081, d77715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76081, d77715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76082 q = 1) (hb : d77716 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76082, d77716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76082, d77716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d76083 q = 1) (hb : d77717 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76083, d77717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76083, d77717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d76084 q = 1) (hb : d77718 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76084, d77718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76084, d77718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76121 q = 1) (hb : d77724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76121, d77724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76121, d77724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8061 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76122 q = 1) (hb : d77725 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76122, d77725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76122, d77725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76123 q = 1) (hb : d77726 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76123, d77726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76123, d77726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d76124 q = 1) (hb : d77727 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76124, d77727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76124, d77727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d76125 q = 1) (hb : d77728 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76125, d77728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76125, d77728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d76126 q = 1) (hb : d77729 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76126, d77729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76126, d77729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8063 (p : Pattern) (ha : d76132 p = 1) (hb : d77735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76127 q = 1) (hb : d77730 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76127, d77730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76127, d77730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8062 q ha hb
  have h2 (q : Pattern) (ha : d76128 q = 1) (hb : d77731 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76128, d77731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76128, d77731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76129 q = 1) (hb : d77732 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76129, d77732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76129, d77732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76130 q = 1) (hb : d77733 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76130, d77733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76130, d77733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76131 q = 1) (hb : d77734 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76131, d77734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76131, d77734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76132 q = 1) (hb : d77735 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76132, d77735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76132, d77735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8064 (p : Pattern) (ha : d76181 p = 1) (hb : d77477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76163 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76169 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d76174 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53064 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6445 q = 1) (hb : d76140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d76140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7546 q ha hb
    | true =>
      simp only [d6445, d76140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76175 q = 1) (hb : d77473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76175, d77473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76175, d77473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d76178 q = 1) (hb : d77474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76178, d77474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76178, d77474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d76179 q = 1) (hb : d77475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76179, d77475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76179, d77475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76180 q = 1) (hb : d77476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76180, d77476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76180, d77476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76181 q = 1) (hb : d77477 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76181, d77477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76181, d77477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8065 (p : Pattern) (ha : d76200 p = 1) (hb : d77484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76163 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76169 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76174 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53064 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6445 q = 1) (hb : d76140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d76140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7546 q ha hb
    | true =>
      simp only [d6445, d76140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76175 q = 1) (hb : d77473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76175, d77473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76175, d77473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76178 q = 1) (hb : d77474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76178, d77474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76178, d77474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76179 q = 1) (hb : d77475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76179, d77475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76179, d77475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76180 q = 1) (hb : d77476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76180, d77476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76180, d77476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d76186 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d76190 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d76193 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53074 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d6466 q = 1) (hb : d76149 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d76149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7549 q ha hb
    | true =>
      simp only [d6466, d76149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76194 q = 1) (hb : d77480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76194, d77480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d76194, d77480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d76197 q = 1) (hb : d77481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76197, d77481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76197, d77481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d76198 q = 1) (hb : d77482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76198, d77482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76198, d77482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d76199 q = 1) (hb : d77483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76199, d77483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76199, d77483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76200 q = 1) (hb : d77484 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76200, d77484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76200, d77484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro8066 (p : Pattern) (ha : d76214 p = 1) (hb : d77741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76193 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53074 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6466 q = 1) (hb : d76149 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d76149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7549 q ha hb
    | true =>
      simp only [d6466, d76149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76194 q = 1) (hb : d77480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76194, d77480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76194, d77480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76197 q = 1) (hb : d77481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76197, d77481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76197, d77481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76212 q = 1) (hb : d77482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76212, d77482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76212, d77482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76213 q = 1) (hb : d77483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76213, d77483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76213, d77483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76214 q = 1) (hb : d77741 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76214, d77741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76214, d77741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8067 (p : Pattern) (ha : d76255 p = 1) (hb : d77751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6525 q = 1) (hb : d76248 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6525, d76248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7554 q ha hb
    | true =>
      simp only [d6525, d76248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76249 q = 1) (hb : d77747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76249, d77747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76249, d77747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76251 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76252 q = 1) (hb : d77748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76252, d77748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76252, d77748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76253 q = 1) (hb : d77749 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76253, d77749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76253, d77749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76254 q = 1) (hb : d77750 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76254, d77750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76254, d77750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76255 q = 1) (hb : d77751 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76255, d77751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76255, d77751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8068 (p : Pattern) (ha : d76261 p = 1) (hb : d77757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76157 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76201 q = 1) (hb : d77485 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76201, d77485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8064 q ha hb
    | true =>
      simp only [d76201, d77485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8065 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76208 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76209 q = 1) (hb : d77486 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76209, d77486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76209, d77486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76210 q = 1) (hb : d77739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76210, d77739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76210, d77739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76211 q = 1) (hb : d77740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76211, d77740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76211, d77740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76215 q = 1) (hb : d77742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76215, d77742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76215, d77742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8066 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76216 q = 1) (hb : d77743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76216, d77743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76216, d77743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76217 q = 1) (hb : d77744 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76217, d77744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76217, d77744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d76218 q = 1) (hb : d77745 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76218, d77745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76218, d77745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d76219 q = 1) (hb : d77746 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76219, d77746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76219, d77746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76256 q = 1) (hb : d77752 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76256, d77752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76256, d77752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8067 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76257 q = 1) (hb : d77753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76257, d77753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76257, d77753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76258 q = 1) (hb : d77754 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76258, d77754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76258, d77754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d76259 q = 1) (hb : d77755 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76259, d77755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76259, d77755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d76260 q = 1) (hb : d77756 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76260, d77756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76260, d77756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d76261 q = 1) (hb : d77757 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76261, d77757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76261, d77757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8069 (p : Pattern) (ha : d76267 p = 1) (hb : d77763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76262 q = 1) (hb : d77758 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76262, d77758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76262, d77758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8068 q ha hb
  have h2 (q : Pattern) (ha : d76263 q = 1) (hb : d77759 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76263, d77759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76263, d77759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76264 q = 1) (hb : d77760 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76264, d77760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76264, d77760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76265 q = 1) (hb : d77761 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76265, d77761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76265, d77761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76266 q = 1) (hb : d77762 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76266, d77762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76266, d77762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76267 q = 1) (hb : d77763 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76267, d77763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76267, d77763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8070 (p : Pattern) (ha : d76317 p = 1) (hb : d77535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76299 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d76310 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6592 q = 1) (hb : d76276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d76276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7558 q ha hb
    | true =>
      simp only [d6592, d76276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76311 q = 1) (hb : d77531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76311, d77531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76311, d77531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d76314 q = 1) (hb : d77532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76314, d77532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76314, d77532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d76315 q = 1) (hb : d77533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76315, d77533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76315, d77533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76316 q = 1) (hb : d77534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76316, d77534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76316, d77534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76317 q = 1) (hb : d77535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76317, d77535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76317, d77535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro8071 (p : Pattern) (ha : d76336 p = 1) (hb : d77542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76310 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6592 q = 1) (hb : d76276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d76276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7558 q ha hb
    | true =>
      simp only [d6592, d76276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76311 q = 1) (hb : d77531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76311, d77531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76311, d77531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76314 q = 1) (hb : d77532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76314, d77532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76314, d77532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76315 q = 1) (hb : d77533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76315, d77533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76315, d77533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76316 q = 1) (hb : d77534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76316, d77534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76316, d77534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d76322 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d76326 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d76329 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53395 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d6613 q = 1) (hb : d76285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d76285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7561 q ha hb
    | true =>
      simp only [d6613, d76285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76330 q = 1) (hb : d77538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76330, d77538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d76330, d77538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d76333 q = 1) (hb : d77539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76333, d77539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76333, d77539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d76334 q = 1) (hb : d77540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76334, d77540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76334, d77540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d76335 q = 1) (hb : d77541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76335, d77541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76335, d77541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d76336 q = 1) (hb : d77542 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76336, d77542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76336, d77542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro8072 (p : Pattern) (ha : d76350 p = 1) (hb : d77770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76329 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53395 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6613 q = 1) (hb : d76285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d76285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7561 q ha hb
    | true =>
      simp only [d6613, d76285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76330 q = 1) (hb : d77538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76330, d77538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76330, d77538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76333 q = 1) (hb : d77539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76333, d77539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76333, d77539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76348 q = 1) (hb : d77540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76348, d77540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76348, d77540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76349 q = 1) (hb : d77541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76349, d77541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76349, d77541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76350 q = 1) (hb : d77770 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76350, d77770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76350, d77770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8073 (p : Pattern) (ha : d76391 p = 1) (hb : d77780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76379 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6672 q = 1) (hb : d76384 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6672, d76384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7566 q ha hb
    | true =>
      simp only [d6672, d76384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76385 q = 1) (hb : d77776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76385, d77776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76385, d77776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76387 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76388 q = 1) (hb : d77777 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76388, d77777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76388, d77777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76389 q = 1) (hb : d77778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76389, d77778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76389, d77778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76390 q = 1) (hb : d77779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76390, d77779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76390, d77779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76391 q = 1) (hb : d77780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76391, d77780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76391, d77780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8074 (p : Pattern) (ha : d76397 p = 1) (hb : d77786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76293 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76337 q = 1) (hb : d77543 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76337, d77543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8070 q ha hb
    | true =>
      simp only [d76337, d77543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8071 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76345 q = 1) (hb : d77544 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76345, d77544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76345, d77544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76346 q = 1) (hb : d77768 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76346, d77768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76346, d77768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76347 q = 1) (hb : d77769 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76347, d77769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76347, d77769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76351 q = 1) (hb : d77771 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76351, d77771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76351, d77771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8072 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76352 q = 1) (hb : d77772 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76352, d77772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76352, d77772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76353 q = 1) (hb : d77773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76353, d77773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76353, d77773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d76354 q = 1) (hb : d77774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76354, d77774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76354, d77774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d76355 q = 1) (hb : d77775 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76355, d77775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76355, d77775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76392 q = 1) (hb : d77781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76392, d77781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76392, d77781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8073 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76393 q = 1) (hb : d77782 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76393, d77782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76393, d77782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76394 q = 1) (hb : d77783 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76394, d77783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76394, d77783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d76395 q = 1) (hb : d77784 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76395, d77784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76395, d77784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d76396 q = 1) (hb : d77785 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76396, d77785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76396, d77785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d76397 q = 1) (hb : d77786 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76397, d77786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76397, d77786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8075 (p : Pattern) (ha : d76403 p = 1) (hb : d77792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76398 q = 1) (hb : d77787 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76398, d77787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76398, d77787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8074 q ha hb
  have h2 (q : Pattern) (ha : d76399 q = 1) (hb : d77788 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76399, d77788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76399, d77788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76400 q = 1) (hb : d77789 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76400, d77789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76400, d77789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76401 q = 1) (hb : d77790 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76401, d77790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76401, d77790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76402 q = 1) (hb : d77791 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76402, d77791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76402, d77791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76403 q = 1) (hb : d77792 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76403, d77792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76403, d77792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8076 (p : Pattern) (ha : d76409 p = 1) (hb : d77798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d75872 q = 1) (hb : d77683 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d75872, d77683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8045 q ha hb
    | true =>
      simp only [d75872, d77683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8051 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75999 q = 1) (hb : d77709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d75999, d77709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75999, d77709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8057 q ha hb
  have h3 (q : Pattern) (ha : d76000 q = 1) (hb : d77710 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76000, d77710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76000, d77710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76133 q = 1) (hb : d77736 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76133, d77736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76133, d77736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8063 q ha hb
  have h5 (q : Pattern) (ha : d76134 q = 1) (hb : d77737 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76134, d77737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76134, d77737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76135 q = 1) (hb : d77738 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76135, d77738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76135, d77738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76268 q = 1) (hb : d77764 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76268, d77764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76268, d77764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8069 q ha hb
  have h8 (q : Pattern) (ha : d76269 q = 1) (hb : d77765 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76269, d77765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76269, d77765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76270 q = 1) (hb : d77766 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76270, d77766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76270, d77766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76271 q = 1) (hb : d77767 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d76271, d77767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76271, d77767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76404 q = 1) (hb : d77793 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76404, d77793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76404, d77793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8075 q ha hb
  have h12 (q : Pattern) (ha : d76405 q = 1) (hb : d77794 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76405, d77794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76405, d77794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76406 q = 1) (hb : d77795 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76406, d77795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76406, d77795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76407 q = 1) (hb : d77796 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d76407, d77796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76407, d77796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76408 q = 1) (hb : d77797 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d76408, d77797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76408, d77797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76409 q = 1) (hb : d77798 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d76409, d77798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76409, d77798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro8077 (p : Pattern) (ha : d76415 p = 1) (hb : d77804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76410 q = 1) (hb : d77799 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d76410, d77799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8076 q ha hb
    | true =>
      simp only [d76410, d77799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76411 q = 1) (hb : d77800 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d76411, d77800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76411, d77800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76412 q = 1) (hb : d77801 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d76412, d77801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76412, d77801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76413 q = 1) (hb : d77802 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d76413, d77802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76413, d77802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76414 q = 1) (hb : d77803 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d76414, d77803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76414, d77803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76415 q = 1) (hb : d77804 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d76415, d77804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76415, d77804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8078 (p : Pattern) (ha : d76421 p = 1) (hb : d77810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76416 q = 1) (hb : d77805 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d76416, d77805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8077 q ha hb
    | true =>
      simp only [d76416, d77805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76417 q = 1) (hb : d77806 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d76417, d77806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76417, d77806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76418 q = 1) (hb : d77807 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d76418, d77807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76418, d77807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76419 q = 1) (hb : d77808 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d76419, d77808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76419, d77808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76420 q = 1) (hb : d77809 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d76420, d77809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76420, d77809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76421 q = 1) (hb : d77810 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d76421, d77810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76421, d77810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8079 (p : Pattern) (ha : d76427 p = 1) (hb : d77816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76422 q = 1) (hb : d77811 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d76422, d77811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8078 q ha hb
    | true =>
      simp only [d76422, d77811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76423 q = 1) (hb : d77812 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d76423, d77812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76423, d77812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76424 q = 1) (hb : d77813 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d76424, d77813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76424, d77813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76425 q = 1) (hb : d77814 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d76425, d77814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76425, d77814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76426 q = 1) (hb : d77815 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d76426, d77815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76426, d77815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76427 q = 1) (hb : d77816 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d76427, d77816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76427, d77816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8080 (p : Pattern) (ha : d76433 p = 1) (hb : d77822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76428 q = 1) (hb : d77817 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d76428, d77817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8079 q ha hb
    | true =>
      simp only [d76428, d77817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76429 q = 1) (hb : d77818 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d76429, d77818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76429, d77818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76430 q = 1) (hb : d77819 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d76430, d77819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76430, d77819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76431 q = 1) (hb : d77820 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d76431, d77820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76431, d77820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76432 q = 1) (hb : d77821 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d76432, d77821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76432, d77821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76433 q = 1) (hb : d77822 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d76433, d77822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76433, d77822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8081 (p : Pattern) (ha : d76439 p = 1) (hb : d77828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76434 q = 1) (hb : d77823 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d76434, d77823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8080 q ha hb
    | true =>
      simp only [d76434, d77823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76435 q = 1) (hb : d77824 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d76435, d77824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76435, d77824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76436 q = 1) (hb : d77825 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d76436, d77825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76436, d77825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76437 q = 1) (hb : d77826 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d76437, d77826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76437, d77826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76438 q = 1) (hb : d77827 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d76438, d77827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76438, d77827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76439 q = 1) (hb : d77828 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d76439, d77828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76439, d77828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8082 (p : Pattern) (ha : d76445 p = 1) (hb : d77834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76440 q = 1) (hb : d77829 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d76440, d77829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8081 q ha hb
    | true =>
      simp only [d76440, d77829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76441 q = 1) (hb : d77830 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d76441, d77830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76441, d77830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76442 q = 1) (hb : d77831 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d76442, d77831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76442, d77831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76443 q = 1) (hb : d77832 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d76443, d77832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76443, d77832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76444 q = 1) (hb : d77833 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d76444, d77833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76444, d77833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76445 q = 1) (hb : d77834 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d76445, d77834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76445, d77834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8083 (p : Pattern) (ha : d76451 p = 1) (hb : d77840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76446 q = 1) (hb : d77835 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d76446, d77835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8082 q ha hb
    | true =>
      simp only [d76446, d77835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76447 q = 1) (hb : d77836 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d76447, d77836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76447, d77836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76448 q = 1) (hb : d77837 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d76448, d77837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76448, d77837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76449 q = 1) (hb : d77838 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d76449, d77838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76449, d77838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76450 q = 1) (hb : d77839 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d76450, d77839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76450, d77839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76451 q = 1) (hb : d77840 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d76451, d77840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76451, d77840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro8084 (p : Pattern) (ha : d104 p = 1) (hb : d76787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5850 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d76783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d76784 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d76785 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d76786 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d76787 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d76787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d76787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8085 (p : Pattern) (ha : d111 p = 1) (hb : d76792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d76783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d76784 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d76785 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d76786 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d5856 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d107 q = 1) (hb : d76788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108 q = 1) (hb : d76789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109 q = 1) (hb : d76790 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d76790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109, d76790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d110 q = 1) (hb : d76791 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d76791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d110, d76791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d111 q = 1) (hb : d76792 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d76792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d111, d76792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro8086 (p : Pattern) (ha : d406 p = 1) (hb : d76799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5856 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d76788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d76789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d76797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d76797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d76797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d76798 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d76798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d76798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d76799 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d76799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d76799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8087 (p : Pattern) (ha : d462 p = 1) (hb : d76809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5874 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d76805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d76805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d76805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d76806 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d76806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d76806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d76807 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d76807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d76807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d76808 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d76808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d76808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d76809 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d76809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d76809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8088 (p : Pattern) (ha : d53647 p = 1) (hb : d76815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d76793 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d76793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8084 q ha hb
    | true =>
      simp only [d112, d76793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8085 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d76794 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d76794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d76794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d76795 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d76795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d76795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d76796 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d76796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d76796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d76800 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d76800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d76800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8086 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d76801 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d76801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d76801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d76802 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d76802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d76802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d76803 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d76803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d76803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d76804 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d76804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d76804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d76810 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d76810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d76810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8087 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d76811 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d76811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d76811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d76812 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d76812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d76812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d76813 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d76813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d76813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d76814 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d76814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d76814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d76815 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d76815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d76815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro8089 (p : Pattern) (ha : d76825 p = 1) (hb : d77255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5911 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5917 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5922 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d4737 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4738 q = 1) (hb : d76821 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4738, d76821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4738, d76821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4739 q = 1) (hb : d76822 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4739, d76822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4739, d76822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4740 q = 1) (hb : d76823 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4740, d76823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4740, d76823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4741 q = 1) (hb : d76824 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4741, d76824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4741, d76824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76825 q = 1) (hb : d77255 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76825, d77255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76825, d77255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro8090 (p : Pattern) (ha : d76830 p = 1) (hb : d77262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5911 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5922 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d4737 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4738 q = 1) (hb : d76821 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4738, d76821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4738, d76821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4739 q = 1) (hb : d76822 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4739, d76822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4739, d76822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4740 q = 1) (hb : d76823 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4740, d76823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4740, d76823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4741 q = 1) (hb : d76824 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4741, d76824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4741, d76824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d5937 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5941 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d5943 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d5356 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d76826 q = 1) (hb : d77258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76826, d77258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76826, d77258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76827 q = 1) (hb : d77259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d77259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76827, d77259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76828 q = 1) (hb : d77260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76828, d77260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76828, d77260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76829 q = 1) (hb : d77261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76829, d77261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76829, d77261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76830 q = 1) (hb : d77262 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76830, d77262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76830, d77262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro8091 (p : Pattern) (ha : d76837 p = 1) (hb : d77635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5943 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76826 q = 1) (hb : d77258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76826, d77258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76826, d77258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76827 q = 1) (hb : d77259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d77259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76827, d77259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76835 q = 1) (hb : d77260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76835, d77260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76835, d77260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76836 q = 1) (hb : d77261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76836, d77261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76836, d77261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76837 q = 1) (hb : d77635 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76837, d77635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76837, d77635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8092 (p : Pattern) (ha : d76847 p = 1) (hb : d77645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5969 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5378 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76843 q = 1) (hb : d77641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76843, d77641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76843, d77641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76844 q = 1) (hb : d77642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76844, d77642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76844, d77642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76845 q = 1) (hb : d77643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76845, d77643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76845, d77643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76846 q = 1) (hb : d77644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76846, d77644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76846, d77644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76847 q = 1) (hb : d77645 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76847, d77645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76847, d77645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8093 (p : Pattern) (ha : d76853 p = 1) (hb : d77651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5905 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76831 q = 1) (hb : d77263 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76831, d77263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8089 q ha hb
    | true =>
      simp only [d76831, d77263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8090 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5953 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76832 q = 1) (hb : d77264 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76832, d77264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76832, d77264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76833 q = 1) (hb : d77633 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76833, d77633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76833, d77633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76834 q = 1) (hb : d77634 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76834, d77634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76834, d77634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76838 q = 1) (hb : d77636 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76838, d77636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76838, d77636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8091 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76839 q = 1) (hb : d77637 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76839, d77637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76839, d77637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76840 q = 1) (hb : d77638 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76840, d77638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76840, d77638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d76841 q = 1) (hb : d77639 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76841, d77639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76841, d77639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d76842 q = 1) (hb : d77640 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76842, d77640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76842, d77640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76848 q = 1) (hb : d77646 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76848, d77646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76848, d77646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8092 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76849 q = 1) (hb : d77647 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76849, d77647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76849, d77647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76850 q = 1) (hb : d77648 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76850, d77648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76850, d77648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d76851 q = 1) (hb : d77649 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76851, d77649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76851, d77649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d76852 q = 1) (hb : d77650 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76852, d77650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76852, d77650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d76853 q = 1) (hb : d77651 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76853, d77651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76853, d77651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8094 (p : Pattern) (ha : d76859 p = 1) (hb : d77657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d76816 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d76816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d76816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8088 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d76817 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d76817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d76817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d76818 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d76818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d76818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d76819 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d76819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d76819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d76820 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d76820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d76820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76854 q = 1) (hb : d77652 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76854, d77652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76854, d77652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8093 q ha hb
  have h8 (q : Pattern) (ha : d76855 q = 1) (hb : d77653 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76855, d77653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76855, d77653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76856 q = 1) (hb : d77654 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76856, d77654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76856, d77654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76857 q = 1) (hb : d77655 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76857, d77655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76857, d77655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76858 q = 1) (hb : d77656 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76858, d77656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76858, d77656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76859 q = 1) (hb : d77657 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76859, d77657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d76859, d77657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8095 (p : Pattern) (ha : d76864 p = 1) (hb : d77309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6014 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6020 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6025 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5400 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76860 q = 1) (hb : d77305 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76860, d77305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76860, d77305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76861 q = 1) (hb : d77306 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d77306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76861, d77306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76862 q = 1) (hb : d77307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d77307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76862, d77307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76863 q = 1) (hb : d77308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d77308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76863, d77308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76864 q = 1) (hb : d77309 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76864, d77309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76864, d77309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8096 (p : Pattern) (ha : d76869 p = 1) (hb : d77316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6020 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6025 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5400 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76860 q = 1) (hb : d77305 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76860, d77305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76860, d77305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76861 q = 1) (hb : d77306 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d77306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76861, d77306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76862 q = 1) (hb : d77307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d77307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76862, d77307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76863 q = 1) (hb : d77308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d77308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76863, d77308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d6040 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d6044 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6047 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d5407 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d76865 q = 1) (hb : d77312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76865, d77312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76865, d77312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76866 q = 1) (hb : d77313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d77313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76866, d77313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76867 q = 1) (hb : d77314 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76867, d77314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76867, d77314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76868 q = 1) (hb : d77315 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76868, d77315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76868, d77315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76869 q = 1) (hb : d77316 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76869, d77316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76869, d77316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro8097 (p : Pattern) (ha : d76876 p = 1) (hb : d77660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6047 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5407 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76865 q = 1) (hb : d77312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76865, d77312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76865, d77312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76866 q = 1) (hb : d77313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d77313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76866, d77313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76874 q = 1) (hb : d77314 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76874, d77314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76874, d77314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76875 q = 1) (hb : d77315 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76875, d77315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76875, d77315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76876 q = 1) (hb : d77660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76876, d77660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76876, d77660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8098 (p : Pattern) (ha : d76886 p = 1) (hb : d77670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5429 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76882 q = 1) (hb : d77666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76882, d77666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76882, d77666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5430 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76883 q = 1) (hb : d77667 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76883, d77667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76883, d77667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76884 q = 1) (hb : d77668 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76884, d77668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76884, d77668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76885 q = 1) (hb : d77669 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76885, d77669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76885, d77669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76886 q = 1) (hb : d77670 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76886, d77670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76886, d77670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8099 (p : Pattern) (ha : d76892 p = 1) (hb : d77676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6008 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76870 q = 1) (hb : d77317 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76870, d77317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8095 q ha hb
    | true =>
      simp only [d76870, d77317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8096 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6062 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76871 q = 1) (hb : d77318 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76871, d77318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76871, d77318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76872 q = 1) (hb : d77658 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76872, d77658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76872, d77658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76873 q = 1) (hb : d77659 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76873, d77659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76873, d77659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76877 q = 1) (hb : d77661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76877, d77661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76877, d77661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8097 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76878 q = 1) (hb : d77662 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76878, d77662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76878, d77662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76879 q = 1) (hb : d77663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76879, d77663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76879, d77663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d76880 q = 1) (hb : d77664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76880, d77664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76880, d77664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d76881 q = 1) (hb : d77665 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76881, d77665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76881, d77665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76887 q = 1) (hb : d77671 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76887, d77671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76887, d77671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8098 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76888 q = 1) (hb : d77672 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76888, d77672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76888, d77672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76889 q = 1) (hb : d77673 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76889, d77673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76889, d77673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d76890 q = 1) (hb : d77674 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76890, d77674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76890, d77674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d76891 q = 1) (hb : d77675 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76891, d77675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76891, d77675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d76892 q = 1) (hb : d77676 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76892, d77676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76892, d77676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8100 (p : Pattern) (ha : d76898 p = 1) (hb : d77682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76893 q = 1) (hb : d77677 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76893, d77677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76893, d77677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8099 q ha hb
  have h2 (q : Pattern) (ha : d76894 q = 1) (hb : d77678 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76894, d77678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76894, d77678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76895 q = 1) (hb : d77679 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76895, d77679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76895, d77679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76896 q = 1) (hb : d77680 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76896, d77680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76896, d77680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76897 q = 1) (hb : d77681 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76897, d77681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76897, d77681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76898 q = 1) (hb : d77682 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76898, d77682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76898, d77682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8101 (p : Pattern) (ha : d76904 p = 1) (hb : d77364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6148 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6153 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6160 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76900 q = 1) (hb : d77360 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76900, d77360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76900, d77360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6161 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76901 q = 1) (hb : d77361 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d77361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76901, d77361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76902 q = 1) (hb : d77362 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d77362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76902, d77362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76903 q = 1) (hb : d77363 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d77363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76903, d77363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76904 q = 1) (hb : d77364 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76904, d77364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76904, d77364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8102 (p : Pattern) (ha : d76909 p = 1) (hb : d77371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6142 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6148 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6153 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6160 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76900 q = 1) (hb : d77360 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76900, d77360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76900, d77360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6161 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76901 q = 1) (hb : d77361 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d77361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76901, d77361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76902 q = 1) (hb : d77362 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d77362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76902, d77362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76903 q = 1) (hb : d77363 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d77363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76903, d77363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d6170 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d6174 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6177 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d6181 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d76905 q = 1) (hb : d77367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76905, d77367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76905, d77367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6182 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76906 q = 1) (hb : d77368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d77368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76906, d77368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76907 q = 1) (hb : d77369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76907, d77369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76907, d77369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76908 q = 1) (hb : d77370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76908, d77370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76908, d77370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76909 q = 1) (hb : d77371 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76909, d77371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76909, d77371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro8103 (p : Pattern) (ha : d76916 p = 1) (hb : d77686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6177 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6181 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76905 q = 1) (hb : d77367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76905, d77367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76905, d77367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6182 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76906 q = 1) (hb : d77368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d77368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76906, d77368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76914 q = 1) (hb : d77369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76914, d77369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76914, d77369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76915 q = 1) (hb : d77370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76915, d77370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76915, d77370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76916 q = 1) (hb : d77686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76916, d77686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76916, d77686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8104 (p : Pattern) (ha : d76926 p = 1) (hb : d77696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6223 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6234 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76922 q = 1) (hb : d77692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76922, d77692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76922, d77692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76923 q = 1) (hb : d77693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76923, d77693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76923, d77693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76924 q = 1) (hb : d77694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76924, d77694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76924, d77694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76925 q = 1) (hb : d77695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76925, d77695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76925, d77695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76926 q = 1) (hb : d77696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76926, d77696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76926, d77696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8105 (p : Pattern) (ha : d76932 p = 1) (hb : d77702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6136 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76910 q = 1) (hb : d77372 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76910, d77372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8101 q ha hb
    | true =>
      simp only [d76910, d77372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8102 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6194 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76911 q = 1) (hb : d77373 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76911, d77373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76911, d77373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76912 q = 1) (hb : d77684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76912, d77684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76912, d77684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76913 q = 1) (hb : d77685 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76913, d77685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76913, d77685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76917 q = 1) (hb : d77687 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76917, d77687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76917, d77687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8103 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76918 q = 1) (hb : d77688 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76918, d77688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76918, d77688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76919 q = 1) (hb : d77689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76919, d77689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76919, d77689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d76920 q = 1) (hb : d77690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76920, d77690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76920, d77690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d76921 q = 1) (hb : d77691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76921, d77691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76921, d77691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76927 q = 1) (hb : d77697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76927, d77697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76927, d77697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8104 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76928 q = 1) (hb : d77698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76928, d77698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76928, d77698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76929 q = 1) (hb : d77699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76929, d77699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76929, d77699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d76930 q = 1) (hb : d77700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76930, d77700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76930, d77700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d76931 q = 1) (hb : d77701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76931, d77701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76931, d77701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d76932 q = 1) (hb : d77702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76932, d77702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76932, d77702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8106 (p : Pattern) (ha : d76938 p = 1) (hb : d77708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76933 q = 1) (hb : d77703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76933, d77703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76933, d77703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8105 q ha hb
  have h2 (q : Pattern) (ha : d76934 q = 1) (hb : d77704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76934, d77704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76934, d77704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76935 q = 1) (hb : d77705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76935, d77705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76935, d77705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76936 q = 1) (hb : d77706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76936, d77706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76936, d77706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76937 q = 1) (hb : d77707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76937, d77707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76937, d77707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76938 q = 1) (hb : d77708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76938, d77708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76938, d77708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8107 (p : Pattern) (ha : d76945 p = 1) (hb : d77420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6281 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6287 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6292 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6299 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76941 q = 1) (hb : d77416 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76941, d77416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76941, d77416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6300 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76942 q = 1) (hb : d77417 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d77417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76942, d77417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76943 q = 1) (hb : d77418 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d77418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76943, d77418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76944 q = 1) (hb : d77419 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d77419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76944, d77419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76945 q = 1) (hb : d77420 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76945, d77420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76945, d77420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8108 (p : Pattern) (ha : d76950 p = 1) (hb : d77427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6281 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6287 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6292 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6299 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76941 q = 1) (hb : d77416 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76941, d77416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76941, d77416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6300 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76942 q = 1) (hb : d77417 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d77417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76942, d77417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76943 q = 1) (hb : d77418 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d77418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76943, d77418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76944 q = 1) (hb : d77419 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d77419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76944, d77419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d6309 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d6313 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6316 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d6320 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d76946 q = 1) (hb : d77423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76946, d77423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76946, d77423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6321 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76947 q = 1) (hb : d77424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d77424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76947, d77424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76948 q = 1) (hb : d77425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76948, d77425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76948, d77425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76949 q = 1) (hb : d77426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76949, d77426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76949, d77426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76950 q = 1) (hb : d77427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76950, d77427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76950, d77427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro8109 (p : Pattern) (ha : d76957 p = 1) (hb : d77713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6316 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6320 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76946 q = 1) (hb : d77423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76946, d77423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76946, d77423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6321 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76947 q = 1) (hb : d77424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d77424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76947, d77424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76955 q = 1) (hb : d77425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76955, d77425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76955, d77425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76956 q = 1) (hb : d77426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76956, d77426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76956, d77426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76957 q = 1) (hb : d77713 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76957, d77713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76957, d77713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8110 (p : Pattern) (ha : d76967 p = 1) (hb : d77723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6368 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6379 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76963 q = 1) (hb : d77719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76963, d77719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76963, d77719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6380 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76964 q = 1) (hb : d77720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76964, d77720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76964, d77720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76965 q = 1) (hb : d77721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76965, d77721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76965, d77721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76966 q = 1) (hb : d77722 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76966, d77722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76966, d77722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76967 q = 1) (hb : d77723 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76967, d77723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76967, d77723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8111 (p : Pattern) (ha : d76973 p = 1) (hb : d77729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76951 q = 1) (hb : d77428 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76951, d77428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8107 q ha hb
    | true =>
      simp only [d76951, d77428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8108 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6333 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76952 q = 1) (hb : d77429 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76952, d77429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76952, d77429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76953 q = 1) (hb : d77711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76953, d77711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76953, d77711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76954 q = 1) (hb : d77712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76954, d77712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76954, d77712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76958 q = 1) (hb : d77714 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76958, d77714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76958, d77714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8109 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76959 q = 1) (hb : d77715 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76959, d77715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76959, d77715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76960 q = 1) (hb : d77716 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76960, d77716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76960, d77716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d76961 q = 1) (hb : d77717 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76961, d77717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76961, d77717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d76962 q = 1) (hb : d77718 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76962, d77718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76962, d77718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76968 q = 1) (hb : d77724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76968, d77724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76968, d77724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8110 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76969 q = 1) (hb : d77725 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76969, d77725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76969, d77725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76970 q = 1) (hb : d77726 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76970, d77726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76970, d77726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d76971 q = 1) (hb : d77727 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76971, d77727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76971, d77727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d76972 q = 1) (hb : d77728 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76972, d77728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76972, d77728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d76973 q = 1) (hb : d77729 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76973, d77729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76973, d77729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8112 (p : Pattern) (ha : d76979 p = 1) (hb : d77735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76974 q = 1) (hb : d77730 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76974, d77730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76974, d77730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8111 q ha hb
  have h2 (q : Pattern) (ha : d76975 q = 1) (hb : d77731 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76975, d77731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76975, d77731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76976 q = 1) (hb : d77732 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76976, d77732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76976, d77732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76977 q = 1) (hb : d77733 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76977, d77733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76977, d77733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76978 q = 1) (hb : d77734 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76978, d77734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76978, d77734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76979 q = 1) (hb : d77735 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76979, d77735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76979, d77735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8113 (p : Pattern) (ha : d76987 p = 1) (hb : d77477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6427 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6433 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6438 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6445 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76983 q = 1) (hb : d77473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76983, d77473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76983, d77473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6446 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76984 q = 1) (hb : d77474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d77474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76984, d77474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76985 q = 1) (hb : d77475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d77475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76985, d77475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76986 q = 1) (hb : d77476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d77476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76986, d77476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76987 q = 1) (hb : d77477 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76987, d77477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76987, d77477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8114 (p : Pattern) (ha : d76992 p = 1) (hb : d77484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6427 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6433 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6438 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6445 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76983 q = 1) (hb : d77473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76983, d77473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76983, d77473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6446 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76984 q = 1) (hb : d77474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d77474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76984, d77474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76985 q = 1) (hb : d77475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d77475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76985, d77475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76986 q = 1) (hb : d77476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d77476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76986, d77476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d6455 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d6459 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6462 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d6466 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d76988 q = 1) (hb : d77480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76988, d77480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76988, d77480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6467 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76989 q = 1) (hb : d77481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d77481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76989, d77481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76990 q = 1) (hb : d77482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76990, d77482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76990, d77482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76991 q = 1) (hb : d77483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76991, d77483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76991, d77483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76992 q = 1) (hb : d77484 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76992, d77484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76992, d77484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro8115 (p : Pattern) (ha : d76999 p = 1) (hb : d77741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6462 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6466 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76988 q = 1) (hb : d77480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76988, d77480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76988, d77480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76989 q = 1) (hb : d77481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d77481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76989, d77481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76997 q = 1) (hb : d77482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76997, d77482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76997, d77482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76998 q = 1) (hb : d77483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76998, d77483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76998, d77483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76999 q = 1) (hb : d77741 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76999, d77741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76999, d77741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8116 (p : Pattern) (ha : d77009 p = 1) (hb : d77751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6514 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6525 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77005 q = 1) (hb : d77747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77005, d77747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77005, d77747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6526 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77006 q = 1) (hb : d77748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77006, d77748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77006, d77748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d77007 q = 1) (hb : d77749 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77007, d77749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77007, d77749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77008 q = 1) (hb : d77750 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77008, d77750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77008, d77750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77009 q = 1) (hb : d77751 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77009, d77751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77009, d77751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8117 (p : Pattern) (ha : d77015 p = 1) (hb : d77757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76993 q = 1) (hb : d77485 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76993, d77485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8113 q ha hb
    | true =>
      simp only [d76993, d77485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8114 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6479 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76994 q = 1) (hb : d77486 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76994, d77486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76994, d77486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76995 q = 1) (hb : d77739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76995, d77739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76995, d77739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76996 q = 1) (hb : d77740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76996, d77740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76996, d77740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77000 q = 1) (hb : d77742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77000, d77742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77000, d77742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8115 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77001 q = 1) (hb : d77743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77001, d77743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77001, d77743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d77002 q = 1) (hb : d77744 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77002, d77744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77002, d77744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77003 q = 1) (hb : d77745 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77003, d77745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77003, d77745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77004 q = 1) (hb : d77746 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77004, d77746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77004, d77746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77010 q = 1) (hb : d77752 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77010, d77752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77010, d77752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8116 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77011 q = 1) (hb : d77753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77011, d77753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77011, d77753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d77012 q = 1) (hb : d77754 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77012, d77754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77012, d77754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77013 q = 1) (hb : d77755 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77013, d77755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77013, d77755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77014 q = 1) (hb : d77756 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77014, d77756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77014, d77756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77015 q = 1) (hb : d77757 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77015, d77757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77015, d77757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8118 (p : Pattern) (ha : d77021 p = 1) (hb : d77763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77016 q = 1) (hb : d77758 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77016, d77758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77016, d77758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8117 q ha hb
  have h2 (q : Pattern) (ha : d77017 q = 1) (hb : d77759 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77017, d77759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77017, d77759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77018 q = 1) (hb : d77760 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77018, d77760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77018, d77760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77019 q = 1) (hb : d77761 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77019, d77761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77019, d77761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77020 q = 1) (hb : d77762 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77020, d77762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77020, d77762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77021 q = 1) (hb : d77763 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77021, d77763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77021, d77763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8119 (p : Pattern) (ha : d77030 p = 1) (hb : d77535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6580 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6585 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6592 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77026 q = 1) (hb : d77531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77026, d77531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d77026, d77531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6593 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d77027 q = 1) (hb : d77532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d77532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77027, d77532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77028 q = 1) (hb : d77533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d77533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d77028, d77533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77029 q = 1) (hb : d77534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d77534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77029, d77534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77030 q = 1) (hb : d77535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77030, d77535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77030, d77535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro8120 (p : Pattern) (ha : d77035 p = 1) (hb : d77542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6580 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6585 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6592 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d77026 q = 1) (hb : d77531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77026, d77531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d77026, d77531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6593 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77027 q = 1) (hb : d77532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d77532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77027, d77532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d77028 q = 1) (hb : d77533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d77533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77028, d77533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77029 q = 1) (hb : d77534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d77534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77029, d77534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d6602 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d6606 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6609 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d6613 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d77031 q = 1) (hb : d77538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77031, d77538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d77031, d77538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6614 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77032 q = 1) (hb : d77539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d77539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77032, d77539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d77033 q = 1) (hb : d77540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77033, d77540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d77033, d77540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77034 q = 1) (hb : d77541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77034, d77541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d77034, d77541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77035 q = 1) (hb : d77542 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77035, d77542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77035, d77542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro8121 (p : Pattern) (ha : d77042 p = 1) (hb : d77770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6609 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6613 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77031 q = 1) (hb : d77538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77031, d77538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77031, d77538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77032 q = 1) (hb : d77539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d77539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77032, d77539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d77040 q = 1) (hb : d77540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77040, d77540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77040, d77540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77041 q = 1) (hb : d77541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77041, d77541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77041, d77541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77042 q = 1) (hb : d77770 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77042, d77770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77042, d77770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8122 (p : Pattern) (ha : d77052 p = 1) (hb : d77780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6661 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77048 q = 1) (hb : d77776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77048, d77776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77048, d77776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6673 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77049 q = 1) (hb : d77777 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77049, d77777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77049, d77777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d77050 q = 1) (hb : d77778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77050, d77778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77050, d77778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77051 q = 1) (hb : d77779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77051, d77779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77051, d77779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77052 q = 1) (hb : d77780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77052, d77780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77052, d77780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8123 (p : Pattern) (ha : d77058 p = 1) (hb : d77786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6568 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77036 q = 1) (hb : d77543 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77036, d77543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8119 q ha hb
    | true =>
      simp only [d77036, d77543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8120 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6626 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77037 q = 1) (hb : d77544 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77037, d77544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77037, d77544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77038 q = 1) (hb : d77768 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77038, d77768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77038, d77768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77039 q = 1) (hb : d77769 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77039, d77769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77039, d77769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77043 q = 1) (hb : d77771 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77043, d77771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77043, d77771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8121 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77044 q = 1) (hb : d77772 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77044, d77772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77044, d77772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d77045 q = 1) (hb : d77773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77045, d77773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77045, d77773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77046 q = 1) (hb : d77774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77046, d77774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77046, d77774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77047 q = 1) (hb : d77775 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77047, d77775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77047, d77775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77053 q = 1) (hb : d77781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77053, d77781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77053, d77781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8122 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77054 q = 1) (hb : d77782 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77054, d77782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77054, d77782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d77055 q = 1) (hb : d77783 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77055, d77783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77055, d77783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77056 q = 1) (hb : d77784 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77056, d77784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77056, d77784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77057 q = 1) (hb : d77785 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77057, d77785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77057, d77785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77058 q = 1) (hb : d77786 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77058, d77786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77058, d77786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro8124 (p : Pattern) (ha : d77064 p = 1) (hb : d77792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77059 q = 1) (hb : d77787 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77059, d77787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77059, d77787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8123 q ha hb
  have h2 (q : Pattern) (ha : d77060 q = 1) (hb : d77788 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77060, d77788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77060, d77788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77061 q = 1) (hb : d77789 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77061, d77789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77061, d77789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77062 q = 1) (hb : d77790 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77062, d77790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77062, d77790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77063 q = 1) (hb : d77791 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77063, d77791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77063, d77791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77064 q = 1) (hb : d77792 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77064, d77792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77064, d77792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8125 (p : Pattern) (ha : d77070 p = 1) (hb : d77798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d76899 q = 1) (hb : d77683 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76899, d77683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8094 q ha hb
    | true =>
      simp only [d76899, d77683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8100 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76939 q = 1) (hb : d77709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76939, d77709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76939, d77709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8106 q ha hb
  have h3 (q : Pattern) (ha : d76940 q = 1) (hb : d77710 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76940, d77710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76940, d77710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76980 q = 1) (hb : d77736 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76980, d77736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76980, d77736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8112 q ha hb
  have h5 (q : Pattern) (ha : d76981 q = 1) (hb : d77737 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76981, d77737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76981, d77737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76982 q = 1) (hb : d77738 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76982, d77738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76982, d77738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77022 q = 1) (hb : d77764 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77022, d77764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77022, d77764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8118 q ha hb
  have h8 (q : Pattern) (ha : d77023 q = 1) (hb : d77765 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77023, d77765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77023, d77765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77024 q = 1) (hb : d77766 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77024, d77766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77024, d77766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77025 q = 1) (hb : d77767 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77025, d77767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77025, d77767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77065 q = 1) (hb : d77793 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77065, d77793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77065, d77793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8124 q ha hb
  have h12 (q : Pattern) (ha : d77066 q = 1) (hb : d77794 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77066, d77794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77066, d77794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77067 q = 1) (hb : d77795 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77067, d77795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77067, d77795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77068 q = 1) (hb : d77796 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77068, d77796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77068, d77796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77069 q = 1) (hb : d77797 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d77069, d77797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77069, d77797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77070 q = 1) (hb : d77798 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d77070, d77798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77070, d77798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro8126 (p : Pattern) (ha : d77076 p = 1) (hb : d77804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77071 q = 1) (hb : d77799 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d77071, d77799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8125 q ha hb
    | true =>
      simp only [d77071, d77799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77072 q = 1) (hb : d77800 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d77072, d77800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77072, d77800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77073 q = 1) (hb : d77801 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d77073, d77801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77073, d77801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77074 q = 1) (hb : d77802 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d77074, d77802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77074, d77802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77075 q = 1) (hb : d77803 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d77075, d77803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77075, d77803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77076 q = 1) (hb : d77804 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d77076, d77804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77076, d77804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8127 (p : Pattern) (ha : d77082 p = 1) (hb : d77810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77077 q = 1) (hb : d77805 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d77077, d77805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8126 q ha hb
    | true =>
      simp only [d77077, d77805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77078 q = 1) (hb : d77806 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d77078, d77806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77078, d77806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77079 q = 1) (hb : d77807 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d77079, d77807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77079, d77807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77080 q = 1) (hb : d77808 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d77080, d77808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77080, d77808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77081 q = 1) (hb : d77809 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d77081, d77809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77081, d77809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77082 q = 1) (hb : d77810 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d77082, d77810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77082, d77810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8128 (p : Pattern) (ha : d77088 p = 1) (hb : d77816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77083 q = 1) (hb : d77811 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d77083, d77811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8127 q ha hb
    | true =>
      simp only [d77083, d77811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77084 q = 1) (hb : d77812 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d77084, d77812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77084, d77812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77085 q = 1) (hb : d77813 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d77085, d77813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77085, d77813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77086 q = 1) (hb : d77814 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d77086, d77814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77086, d77814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77087 q = 1) (hb : d77815 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d77087, d77815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77087, d77815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77088 q = 1) (hb : d77816 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d77088, d77816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77088, d77816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8129 (p : Pattern) (ha : d77094 p = 1) (hb : d77822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77089 q = 1) (hb : d77817 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d77089, d77817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8128 q ha hb
    | true =>
      simp only [d77089, d77817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77090 q = 1) (hb : d77818 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d77090, d77818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77090, d77818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77091 q = 1) (hb : d77819 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d77091, d77819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77091, d77819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77092 q = 1) (hb : d77820 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d77092, d77820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77092, d77820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77093 q = 1) (hb : d77821 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d77093, d77821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77093, d77821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77094 q = 1) (hb : d77822 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d77094, d77822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77094, d77822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8130 (p : Pattern) (ha : d77100 p = 1) (hb : d77828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77095 q = 1) (hb : d77823 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d77095, d77823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8129 q ha hb
    | true =>
      simp only [d77095, d77823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77096 q = 1) (hb : d77824 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d77096, d77824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77096, d77824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77097 q = 1) (hb : d77825 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d77097, d77825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77097, d77825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77098 q = 1) (hb : d77826 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d77098, d77826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77098, d77826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77099 q = 1) (hb : d77827 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d77099, d77827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77099, d77827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77100 q = 1) (hb : d77828 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d77100, d77828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77100, d77828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8131 (p : Pattern) (ha : d77106 p = 1) (hb : d77834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77101 q = 1) (hb : d77829 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d77101, d77829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8130 q ha hb
    | true =>
      simp only [d77101, d77829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77102 q = 1) (hb : d77830 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d77102, d77830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77102, d77830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77103 q = 1) (hb : d77831 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d77103, d77831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77103, d77831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77104 q = 1) (hb : d77832 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d77104, d77832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77104, d77832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77105 q = 1) (hb : d77833 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d77105, d77833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77105, d77833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77106 q = 1) (hb : d77834 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d77106, d77834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77106, d77834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8132 (p : Pattern) (ha : d77112 p = 1) (hb : d77840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77107 q = 1) (hb : d77835 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d77107, d77835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8131 q ha hb
    | true =>
      simp only [d77107, d77835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77108 q = 1) (hb : d77836 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d77108, d77836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77108, d77836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77109 q = 1) (hb : d77837 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d77109, d77837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77109, d77837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77110 q = 1) (hb : d77838 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d77110, d77838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77110, d77838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77111 q = 1) (hb : d77839 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d77111, d77839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77111, d77839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77112 q = 1) (hb : d77840 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d77112, d77840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77112, d77840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8133 (p : Pattern) (ha : d42 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d39, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
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
theorem andIntro8134 (p : Pattern) (ha : d48 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8133 q ha hb
    | true =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d48 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8135 (p : Pattern) (ha : d49 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d39 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d39, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8136 (p : Pattern) (ha : d55 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8133 q ha hb
    | true =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d50 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8135 q ha hb
    | true =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d51 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d55 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8137 (p : Pattern) (ha : d60 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8135 q ha hb
    | true =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d52 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8138 (p : Pattern) (ha : d83 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d80 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8139 (p : Pattern) (ha : d89 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8138 q ha hb
    | true =>
      simp only [d84, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d86 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d87 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8140 (p : Pattern) (ha : d95 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8134 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8136 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8137 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8139 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
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
theorem andIntro8141 (p : Pattern) (ha : d104 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8133 q ha hb
    | true =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d104 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8142 (p : Pattern) (ha : d111 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8133 q ha hb
    | true =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d50 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8135 q ha hb
    | true =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d107 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d109 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d110 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d111 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8143 (p : Pattern) (ha : d213 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8133 q ha hb
    | true =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d213 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro8144 (p : Pattern) (ha : d116 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d39, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
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
theorem andIntro8145 (p : Pattern) (ha : d123 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d39, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
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
theorem andIntro8146 (p : Pattern) (ha : d156 p = 1) (hb : d77844 p = 1) : d79651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d153 q = 1) (hb : d77844 q = 1) : d79648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d153, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d154 q = 1) (hb : d77844 q = 1) : d79649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d154, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d155 q = 1) (hb : d77844 q = 1) : d79650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d156 q = 1) (hb : d77844 q = 1) : d79651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d79651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d79651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8147 (p : Pattern) (ha : d69436 p = 1) (hb : d77845 p = 1) : d79657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d117 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8144 q ha hb
    | true =>
      simp only [d117, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d124 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8145 q ha hb
    | true =>
      simp only [d124, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d125 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d370 q = 1) (hb : d77845 q = 1) : d79652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8146 q ha hb
    | true =>
      simp only [d370, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d371 q = 1) (hb : d77845 q = 1) : d79653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d371, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8133 q ha hb
    | true =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69433 q = 1) (hb : d77845 q = 1) : d79654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69433, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69433, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69434 q = 1) (hb : d77845 q = 1) : d79655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69434, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69434, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69435 q = 1) (hb : d77845 q = 1) : d79656 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69435, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69435, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69436 q = 1) (hb : d77845 q = 1) : d79657 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69436, d79657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69436, d79657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro8148 (p : Pattern) (ha : d194 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d39, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
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
theorem andIntro8149 (p : Pattern) (ha : d199 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d39, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
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
theorem andIntro8150 (p : Pattern) (ha : d203 p = 1) (hb : d77844 p = 1) : d79658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d153 q = 1) (hb : d77844 q = 1) : d79648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d153, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d154 q = 1) (hb : d77844 q = 1) : d79649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d154, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155 q = 1) (hb : d77844 q = 1) : d79650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d203 q = 1) (hb : d77844 q = 1) : d79658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d79658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d203, d79658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8151 (p : Pattern) (ha : d69440 p = 1) (hb : d77845 p = 1) : d79664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d117 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8144 q ha hb
    | true =>
      simp only [d117, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d124 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8145 q ha hb
    | true =>
      simp only [d124, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d125 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d370 q = 1) (hb : d77845 q = 1) : d79652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8146 q ha hb
    | true =>
      simp only [d370, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d371 q = 1) (hb : d77845 q = 1) : d79653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d371, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8133 q ha hb
    | true =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69433 q = 1) (hb : d77845 q = 1) : d79654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69433, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69433, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69434 q = 1) (hb : d77845 q = 1) : d79655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69434, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69434, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69435 q = 1) (hb : d77845 q = 1) : d79656 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69435, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69435, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8148 q ha hb
    | true =>
      simp only [d195, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d196 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d197 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d198 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8149 q ha hb
    | true =>
      simp only [d200, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d201 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d202 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d390 q = 1) (hb : d77845 q = 1) : d79659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8150 q ha hb
    | true =>
      simp only [d390, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d391 q = 1) (hb : d77845 q = 1) : d79660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d391, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d50 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8135 q ha hb
    | true =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d51 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d69437 q = 1) (hb : d77845 q = 1) : d79661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69437, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69437, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d69438 q = 1) (hb : d77845 q = 1) : d79662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69438, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d69438, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d69439 q = 1) (hb : d77845 q = 1) : d79663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69439, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d69439, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d69440 q = 1) (hb : d77845 q = 1) : d79664 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69440, d79664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69440, d79664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  exact h30 p ha hb
theorem andIntro8152 (p : Pattern) (ha : d69447 p = 1) (hb : d77845 p = 1) : d79669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d390 q = 1) (hb : d77845 q = 1) : d79659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8150 q ha hb
    | true =>
      simp only [d390, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d391 q = 1) (hb : d77845 q = 1) : d79660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d391, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d50 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8135 q ha hb
    | true =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69437 q = 1) (hb : d77845 q = 1) : d79661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69437, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69437, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69445 q = 1) (hb : d77845 q = 1) : d79662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69445, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69445, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69446 q = 1) (hb : d77845 q = 1) : d79663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69446, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69446, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69447 q = 1) (hb : d77845 q = 1) : d79669 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69447, d79669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69447, d79669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8153 (p : Pattern) (ha : d243 p = 1) (hb : d77844 p = 1) : d79678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d239 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79 q = 1) (hb : d77842 q = 1) : d79 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d240 q = 1) (hb : d77844 q = 1) : d79675 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d77844, d79675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d240, d77844, d79675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d241 q = 1) (hb : d77844 q = 1) : d79676 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d79676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d241, d79676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242 q = 1) (hb : d77844 q = 1) : d79677 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d79677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242, d79677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d243 q = 1) (hb : d77844 q = 1) : d79678 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d79678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243, d79678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8154 (p : Pattern) (ha : d69456 p = 1) (hb : d77845 p = 1) : d79684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d451 q = 1) (hb : d77845 q = 1) : d79679 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d451, d77845, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8153 q ha hb
    | true =>
      simp only [d451, d77845, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d452 q = 1) (hb : d77845 q = 1) : d79680 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d452, d79680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d452, d79680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d84 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8138 q ha hb
    | true =>
      simp only [d84, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69453 q = 1) (hb : d77845 q = 1) : d79681 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69453, d79681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69453, d79681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69454 q = 1) (hb : d77845 q = 1) : d79682 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69454, d79682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69454, d79682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69455 q = 1) (hb : d77845 q = 1) : d79683 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69455, d79683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69455, d79683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69456 q = 1) (hb : d77845 q = 1) : d79684 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69456, d79684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69456, d79684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8155 (p : Pattern) (ha : d69972 p = 1) (hb : d77845 p = 1) : d79690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8141 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8141 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8142 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69441 q = 1) (hb : d77845 q = 1) : d79665 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69441, d79665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8147 q ha hb
    | true =>
      simp only [d69441, d79665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8151 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8143 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69968 q = 1) (hb : d77845 q = 1) : d79666 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69968, d79666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69968, d79666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69969 q = 1) (hb : d77845 q = 1) : d79667 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69969, d79667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69969, d79667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d69970 q = 1) (hb : d77845 q = 1) : d79668 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69970, d79668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69970, d79668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69448 q = 1) (hb : d77845 q = 1) : d79670 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69448, d79670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69448, d79670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8152 q ha hb
  have h12 (q : Pattern) (ha : d69449 q = 1) (hb : d77845 q = 1) : d79671 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69449, d79671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69449, d79671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69450 q = 1) (hb : d77845 q = 1) : d79672 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69450, d79672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69450, d79672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69451 q = 1) (hb : d77845 q = 1) : d79673 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69451, d79673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69451, d79673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69971 q = 1) (hb : d77845 q = 1) : d79674 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69971, d79674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69971, d79674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69457 q = 1) (hb : d77845 q = 1) : d79685 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69457, d79685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69457, d79685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8154 q ha hb
  have h17 (q : Pattern) (ha : d69458 q = 1) (hb : d77845 q = 1) : d79686 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69458, d79686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d69458, d79686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d69459 q = 1) (hb : d77845 q = 1) : d79687 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69459, d79687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d69459, d79687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d69460 q = 1) (hb : d77845 q = 1) : d79688 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69460, d79688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d69460, d79688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69461 q = 1) (hb : d77845 q = 1) : d79689 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69461, d79689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d69461, d79689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d69972 q = 1) (hb : d77845 q = 1) : d79690 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69972, d79690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69972, d79690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro8156 (p : Pattern) (ha : d406 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8135 q ha hb
    | true =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d110 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d406 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8157 (p : Pattern) (ha : d462 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8138 q ha hb
    | true =>
      simp only [d84, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d459 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d460 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d461 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d462 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8158 (p : Pattern) (ha : d4693 p = 1) (hb : d77845 p = 1) : d79700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d370 q = 1) (hb : d77845 q = 1) : d79652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8146 q ha hb
    | true =>
      simp only [d370, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4689 q = 1) (hb : d77845 q = 1) : d79696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4689, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4689, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4690 q = 1) (hb : d77845 q = 1) : d79697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4690, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4690, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4691 q = 1) (hb : d77845 q = 1) : d79698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4691, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4691, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4692 q = 1) (hb : d77845 q = 1) : d79699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4692, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4692, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4693 q = 1) (hb : d77845 q = 1) : d79700 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4693, d79700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4693, d79700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8159 (p : Pattern) (ha : d4700 p = 1) (hb : d77845 p = 1) : d79707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d370 q = 1) (hb : d77845 q = 1) : d79652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8146 q ha hb
    | true =>
      simp only [d370, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4689 q = 1) (hb : d77845 q = 1) : d79696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4689, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4689, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4690 q = 1) (hb : d77845 q = 1) : d79697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4690, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4690, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4691 q = 1) (hb : d77845 q = 1) : d79698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4691, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4691, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4692 q = 1) (hb : d77845 q = 1) : d79699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4692, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4692, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d390 q = 1) (hb : d77845 q = 1) : d79659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8150 q ha hb
    | true =>
      simp only [d390, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d4696 q = 1) (hb : d77845 q = 1) : d79703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4696, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4696, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4697 q = 1) (hb : d77845 q = 1) : d79704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4697, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4697, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4698 q = 1) (hb : d77845 q = 1) : d79705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4698, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4698, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4699 q = 1) (hb : d77845 q = 1) : d79706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4699, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4699, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4700 q = 1) (hb : d77845 q = 1) : d79707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4700, d79707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4700, d79707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8160 (p : Pattern) (ha : d4736 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4733, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8161 (p : Pattern) (ha : d4742 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4737 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8160 q ha hb
    | true =>
      simp only [d4737, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4738 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4739 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4740 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4741 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8133 q ha hb
    | true =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d100 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d102 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d103 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4742 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8162 (p : Pattern) (ha : d296 p = 1) (hb : d77844 p = 1) : d79712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d153 q = 1) (hb : d77844 q = 1) : d79648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d153, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d154 q = 1) (hb : d77844 q = 1) : d79649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d154, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d295 q = 1) (hb : d77844 q = 1) : d79711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d296 q = 1) (hb : d77844 q = 1) : d79712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d79712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d79712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8163 (p : Pattern) (ha : d303 p = 1) (hb : d77844 p = 1) : d79719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d153 q = 1) (hb : d77844 q = 1) : d79648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d153, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d301 q = 1) (hb : d77844 q = 1) : d79717 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d302 q = 1) (hb : d77844 q = 1) : d79718 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d302, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d303 q = 1) (hb : d77844 q = 1) : d79719 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d79719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d79719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8164 (p : Pattern) (ha : d150 p = 1) (hb : d77842 p = 1) : d7241 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d148 q = 1) : d148 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d149 q = 1) (hb : d77842 q = 1) : d7240 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d77842, d7240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d149, d77842, d7240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150 q = 1) (hb : d77842 q = 1) : d7241 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d7241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150, d7241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro8165 (p : Pattern) (ha : d336 p = 1) (hb : d77844 p = 1) : d79726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d332 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d333 q = 1) (hb : d77844 q = 1) : d79723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d77844, d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333, d77844, d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d334 q = 1) (hb : d77844 q = 1) : d79724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d334, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d335 q = 1) (hb : d77844 q = 1) : d79725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d335, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d336 q = 1) (hb : d77844 q = 1) : d79726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336, d79726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d336, d79726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8166 (p : Pattern) (ha : d69472 p = 1) (hb : d77845 p = 1) : d79732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4704 q = 1) (hb : d77845 q = 1) : d79713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4704, d77845, d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8162 q ha hb
    | true =>
      simp only [d4704, d77845, d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4705 q = 1) (hb : d77845 q = 1) : d79714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4705, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4705, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4706 q = 1) (hb : d77845 q = 1) : d79715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4706, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4706, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4707 q = 1) (hb : d77845 q = 1) : d79716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4707, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4707, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4708 q = 1) (hb : d77845 q = 1) : d79720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4708, d77845, d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8163 q ha hb
    | true =>
      simp only [d4708, d77845, d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d4709 q = 1) (hb : d77845 q = 1) : d79721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4709, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4709, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4710 q = 1) (hb : d77845 q = 1) : d79722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4710, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4710, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4711 q = 1) (hb : d77845 q = 1) : d79727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4711, d77845, d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8165 q ha hb
    | true =>
      simp only [d4711, d77845, d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d69468 q = 1) (hb : d77845 q = 1) : d79728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69468, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69468, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d370 q = 1) (hb : d77845 q = 1) : d79652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8146 q ha hb
    | true =>
      simp only [d370, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d371 q = 1) (hb : d77845 q = 1) : d79653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d371, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69469 q = 1) (hb : d77845 q = 1) : d79729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69469, d79729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69469, d79729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69470 q = 1) (hb : d77845 q = 1) : d79730 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69470, d79730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69470, d79730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69471 q = 1) (hb : d77845 q = 1) : d79731 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69471, d79731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69471, d79731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69472 q = 1) (hb : d77845 q = 1) : d79732 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69472, d79732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69472, d79732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro8167 (p : Pattern) (ha : d376 p = 1) (hb : d77844 p = 1) : d79733 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d153 q = 1) (hb : d77844 q = 1) : d79648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d153, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d154 q = 1) (hb : d77844 q = 1) : d79649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d154, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d295 q = 1) (hb : d77844 q = 1) : d79711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d376 q = 1) (hb : d77844 q = 1) : d79733 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d79733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d376, d79733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8168 (p : Pattern) (ha : d381 p = 1) (hb : d77844 p = 1) : d79738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d153 q = 1) (hb : d77844 q = 1) : d79648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d153, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d301 q = 1) (hb : d77844 q = 1) : d79717 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d302 q = 1) (hb : d77844 q = 1) : d79718 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d302, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d381 q = 1) (hb : d77844 q = 1) : d79738 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d79738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d381, d79738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8169 (p : Pattern) (ha : d385 p = 1) (hb : d77844 p = 1) : d79742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d332 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d333 q = 1) (hb : d77844 q = 1) : d79723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d77844, d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333, d77844, d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d334 q = 1) (hb : d77844 q = 1) : d79724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d334, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d335 q = 1) (hb : d77844 q = 1) : d79725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d335, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d385 q = 1) (hb : d77844 q = 1) : d79742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d385, d79742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d385, d79742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro8170 (p : Pattern) (ha : d69477 p = 1) (hb : d77845 p = 1) : d79748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4704 q = 1) (hb : d77845 q = 1) : d79713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4704, d77845, d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8162 q ha hb
    | true =>
      simp only [d4704, d77845, d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4705 q = 1) (hb : d77845 q = 1) : d79714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4705, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4705, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4706 q = 1) (hb : d77845 q = 1) : d79715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4706, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4706, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4707 q = 1) (hb : d77845 q = 1) : d79716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4707, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4707, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4708 q = 1) (hb : d77845 q = 1) : d79720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4708, d77845, d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8163 q ha hb
    | true =>
      simp only [d4708, d77845, d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d4709 q = 1) (hb : d77845 q = 1) : d79721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4709, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4709, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4710 q = 1) (hb : d77845 q = 1) : d79722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4710, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4710, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4711 q = 1) (hb : d77845 q = 1) : d79727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4711, d77845, d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8165 q ha hb
    | true =>
      simp only [d4711, d77845, d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d69468 q = 1) (hb : d77845 q = 1) : d79728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69468, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69468, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d370 q = 1) (hb : d77845 q = 1) : d79652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8146 q ha hb
    | true =>
      simp only [d370, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d371 q = 1) (hb : d77845 q = 1) : d79653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d371, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69469 q = 1) (hb : d77845 q = 1) : d79729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69469, d79729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69469, d79729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69470 q = 1) (hb : d77845 q = 1) : d79730 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69470, d79730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69470, d79730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69471 q = 1) (hb : d77845 q = 1) : d79731 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69471, d79731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69471, d79731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4718 q = 1) (hb : d77845 q = 1) : d79734 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4718, d77845, d79734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8167 q ha hb
    | true =>
      simp only [d4718, d77845, d79734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d4719 q = 1) (hb : d77845 q = 1) : d79735 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4719, d79735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4719, d79735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4720 q = 1) (hb : d77845 q = 1) : d79736 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4720, d79736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4720, d79736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4721 q = 1) (hb : d77845 q = 1) : d79737 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4721, d79737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4721, d79737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d4722 q = 1) (hb : d77845 q = 1) : d79739 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4722, d77845, d79739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8168 q ha hb
    | true =>
      simp only [d4722, d77845, d79739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d4723 q = 1) (hb : d77845 q = 1) : d79740 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4723, d79740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4723, d79740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d4724 q = 1) (hb : d77845 q = 1) : d79741 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4724, d79741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4724, d79741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d4725 q = 1) (hb : d77845 q = 1) : d79743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4725, d77845, d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8169 q ha hb
    | true =>
      simp only [d4725, d77845, d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d69473 q = 1) (hb : d77845 q = 1) : d79744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69473, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d69473, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d390 q = 1) (hb : d77845 q = 1) : d79659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8150 q ha hb
    | true =>
      simp only [d390, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d391 q = 1) (hb : d77845 q = 1) : d79660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d391, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d69474 q = 1) (hb : d77845 q = 1) : d79745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69474, d79745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69474, d79745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d69475 q = 1) (hb : d77845 q = 1) : d79746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69475, d79746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d69475, d79746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d69476 q = 1) (hb : d77845 q = 1) : d79747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69476, d79747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d69476, d79747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d69477 q = 1) (hb : d77845 q = 1) : d79748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69477, d79748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69477, d79748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  exact h30 p ha hb
theorem andIntro8171 (p : Pattern) (ha : d69484 p = 1) (hb : d77845 p = 1) : d79755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4725 q = 1) (hb : d77845 q = 1) : d79743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4725, d77845, d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8169 q ha hb
    | true =>
      simp only [d4725, d77845, d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69473 q = 1) (hb : d77845 q = 1) : d79744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69473, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69473, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d390 q = 1) (hb : d77845 q = 1) : d79659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8150 q ha hb
    | true =>
      simp only [d390, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d391 q = 1) (hb : d77845 q = 1) : d79660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d391, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69474 q = 1) (hb : d77845 q = 1) : d79745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69474, d79745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69474, d79745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69482 q = 1) (hb : d77845 q = 1) : d79753 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69482, d79753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69482, d79753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69483 q = 1) (hb : d77845 q = 1) : d79754 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69483, d79754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69483, d79754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69484 q = 1) (hb : d77845 q = 1) : d79755 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69484, d79755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69484, d79755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8172 (p : Pattern) (ha : d237 p = 1) (hb : d77842 p = 1) : d7274 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d235 q = 1) : d235 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d236 q = 1) (hb : d77842 q = 1) : d7273 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d77842, d7273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236, d77842, d7273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237 q = 1) (hb : d77842 q = 1) : d7274 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d7274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237, d7274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro8173 (p : Pattern) (ha : d429 p = 1) (hb : d77844 p = 1) : d79764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d425 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d238 q = 1) (hb : d77842 q = 1) : d7275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d7275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8172 q ha hb
    | true =>
      simp only [d238, d7275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d239 q = 1) (hb : d77842 q = 1) : d7276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d7276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239, d7276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d426 q = 1) (hb : d77844 q = 1) : d79761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d426, d77844, d79761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d426, d77844, d79761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d427 q = 1) (hb : d77844 q = 1) : d79762 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d427, d79762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d427, d79762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d428 q = 1) (hb : d77844 q = 1) : d79763 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d428, d79763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d428, d79763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d429 q = 1) (hb : d77844 q = 1) : d79764 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d429, d79764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d429, d79764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro8174 (p : Pattern) (ha : d69494 p = 1) (hb : d77845 p = 1) : d79770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4755 q = 1) (hb : d77845 q = 1) : d79765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4755, d77845, d79765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8173 q ha hb
    | true =>
      simp only [d4755, d77845, d79765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69490 q = 1) (hb : d77845 q = 1) : d79766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69490, d79766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69490, d79766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d451 q = 1) (hb : d77845 q = 1) : d79679 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d451, d77845, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8153 q ha hb
    | true =>
      simp only [d451, d77845, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d452 q = 1) (hb : d77845 q = 1) : d79680 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d452, d79680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d452, d79680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69491 q = 1) (hb : d77845 q = 1) : d79767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69491, d79767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69491, d79767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69492 q = 1) (hb : d77845 q = 1) : d79768 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69492, d79768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69492, d79768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69493 q = 1) (hb : d77845 q = 1) : d79769 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69493, d79769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69493, d79769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69494 q = 1) (hb : d77845 q = 1) : d79770 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69494, d79770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69494, d79770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8175 (p : Pattern) (ha : d69989 p = 1) (hb : d77845 p = 1) : d79776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4694 q = 1) (hb : d77845 q = 1) : d79701 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4694, d79701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4694, d79701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8158 q ha hb
  have h2 (q : Pattern) (ha : d4695 q = 1) (hb : d77845 q = 1) : d79702 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4695, d79702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4695, d79702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4701 q = 1) (hb : d77845 q = 1) : d79708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4701, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8158 q ha hb
    | true =>
      simp only [d4701, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8159 q ha hb
  have h4 (q : Pattern) (ha : d4702 q = 1) (hb : d77845 q = 1) : d79709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4702, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4702, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4703 q = 1) (hb : d77845 q = 1) : d79710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4703, d79710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4703, d79710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69478 q = 1) (hb : d77845 q = 1) : d79749 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69478, d79749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8166 q ha hb
    | true =>
      simp only [d69478, d79749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8170 q ha hb
  have h7 (q : Pattern) (ha : d4743 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8161 q ha hb
    | true =>
      simp only [d4743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8142 q ha hb
  have h8 (q : Pattern) (ha : d69978 q = 1) (hb : d77845 q = 1) : d79750 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69978, d79750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69978, d79750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69979 q = 1) (hb : d77845 q = 1) : d79751 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69979, d79751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69979, d79751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d69980 q = 1) (hb : d77845 q = 1) : d79752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69980, d79752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69980, d79752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69485 q = 1) (hb : d77845 q = 1) : d79756 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69485, d79756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69485, d79756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8171 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8156 q ha hb
  have h13 (q : Pattern) (ha : d69981 q = 1) (hb : d77845 q = 1) : d79757 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69981, d79757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69981, d79757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69982 q = 1) (hb : d77845 q = 1) : d79758 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69982, d79758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69982, d79758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69983 q = 1) (hb : d77845 q = 1) : d79759 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69983, d79759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d69983, d79759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d69984 q = 1) (hb : d77845 q = 1) : d79760 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69984, d79760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69984, d79760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69495 q = 1) (hb : d77845 q = 1) : d79771 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69495, d79771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69495, d79771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8174 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8157 q ha hb
  have h19 (q : Pattern) (ha : d69985 q = 1) (hb : d77845 q = 1) : d79772 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69985, d79772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d69985, d79772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d69986 q = 1) (hb : d77845 q = 1) : d79773 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69986, d79773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d69986, d79773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d69987 q = 1) (hb : d77845 q = 1) : d79774 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69987, d79774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d69987, d79774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d69988 q = 1) (hb : d77845 q = 1) : d79775 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69988, d79775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d69988, d79775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d69989 q = 1) (hb : d77845 q = 1) : d79776 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69989, d79776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d69989, d79776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro8176 (p : Pattern) (ha : d69995 p = 1) (hb : d77845 p = 1) : d79782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8140 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69973 q = 1) (hb : d77845 q = 1) : d79691 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69973, d79691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69973, d79691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8155 q ha hb
  have h6 (q : Pattern) (ha : d69974 q = 1) (hb : d77845 q = 1) : d79692 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69974, d79692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69974, d79692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69975 q = 1) (hb : d77845 q = 1) : d79693 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69975, d79693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69975, d79693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69976 q = 1) (hb : d77845 q = 1) : d79694 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69976, d79694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69976, d79694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69977 q = 1) (hb : d77845 q = 1) : d79695 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69977, d79695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69977, d79695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69990 q = 1) (hb : d77845 q = 1) : d79777 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69990, d79777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69990, d79777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8175 q ha hb
  have h11 (q : Pattern) (ha : d69991 q = 1) (hb : d77845 q = 1) : d79778 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69991, d79778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69991, d79778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69992 q = 1) (hb : d77845 q = 1) : d79779 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69992, d79779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69992, d79779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69993 q = 1) (hb : d77845 q = 1) : d79780 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69993, d79780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69993, d79780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69994 q = 1) (hb : d77845 q = 1) : d79781 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69994, d79781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69994, d79781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69995 q = 1) (hb : d77845 q = 1) : d79782 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69995, d79782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69995, d79782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro8177 (p : Pattern) (ha : d491 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d488, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8178 (p : Pattern) (ha : d501 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d488 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d488, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8179 (p : Pattern) (ha : d644 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d633 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8177 q ha hb
    | true =>
      simp only [d633, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d634 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d635 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d636 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d637 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d639 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8178 q ha hb
    | true =>
      simp only [d639, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d640 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d641 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d642 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d643 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d644 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8180 (p : Pattern) (ha : d653 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d639 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8178 q ha hb
    | true =>
      simp only [d639, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d640 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d641 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d642 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d643 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d653 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8181 (p : Pattern) (ha : d730 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d685 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d727 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d727, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8182 (p : Pattern) (ha : d736 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d731 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8181 q ha hb
    | true =>
      simp only [d731, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d732 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d733 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d734 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d735 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d736 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8183 (p : Pattern) (ha : d487 p = 1) (hb : d77844 p = 1) : d79786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d484 q = 1) (hb : d77844 q = 1) : d79783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d484, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d485 q = 1) (hb : d77844 q = 1) : d79784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d485, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d486 q = 1) (hb : d77844 q = 1) : d79785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d486, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d486, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d487 q = 1) (hb : d77844 q = 1) : d79786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d487, d79786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d487, d79786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8184 (p : Pattern) (ha : d4778 p = 1) (hb : d77845 p = 1) : d79792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d603 q = 1) (hb : d77845 q = 1) : d79787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8183 q ha hb
    | true =>
      simp only [d603, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4774 q = 1) (hb : d77845 q = 1) : d79788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4774, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4774, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4775 q = 1) (hb : d77845 q = 1) : d79789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4775, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4775, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4776 q = 1) (hb : d77845 q = 1) : d79790 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4776, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4776, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4777 q = 1) (hb : d77845 q = 1) : d79791 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4777, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4777, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4778 q = 1) (hb : d77845 q = 1) : d79792 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4778, d79792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4778, d79792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8185 (p : Pattern) (ha : d500 p = 1) (hb : d77844 p = 1) : d79795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d484 q = 1) (hb : d77844 q = 1) : d79783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d484, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d485 q = 1) (hb : d77844 q = 1) : d79784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d485, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d486 q = 1) (hb : d77844 q = 1) : d79785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d486, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d486, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d500 q = 1) (hb : d77844 q = 1) : d79795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d500, d79795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d500, d79795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8186 (p : Pattern) (ha : d4785 p = 1) (hb : d77845 p = 1) : d79801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d603 q = 1) (hb : d77845 q = 1) : d79787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8183 q ha hb
    | true =>
      simp only [d603, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4774 q = 1) (hb : d77845 q = 1) : d79788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4774, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4774, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4775 q = 1) (hb : d77845 q = 1) : d79789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4775, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4775, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4776 q = 1) (hb : d77845 q = 1) : d79790 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4776, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4776, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4777 q = 1) (hb : d77845 q = 1) : d79791 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4777, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4777, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d626 q = 1) (hb : d77845 q = 1) : d79796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d77845, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8185 q ha hb
    | true =>
      simp only [d626, d77845, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d4781 q = 1) (hb : d77845 q = 1) : d79797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4781, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4781, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4782 q = 1) (hb : d77845 q = 1) : d79798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4782, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4782, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4783 q = 1) (hb : d77845 q = 1) : d79799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4783, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4783, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4784 q = 1) (hb : d77845 q = 1) : d79800 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4784, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4784, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4785 q = 1) (hb : d77845 q = 1) : d79801 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4785, d79801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4785, d79801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8187 (p : Pattern) (ha : d4830 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4827 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4827, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4827, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4828 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4829 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4830 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8188 (p : Pattern) (ha : d4836 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4831 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4831, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8187 q ha hb
    | true =>
      simp only [d4831, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4832 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4833 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4834 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4835 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d633 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8177 q ha hb
    | true =>
      simp only [d633, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d634 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d635 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d636 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d637 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4836 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8189 (p : Pattern) (ha : d512 p = 1) (hb : d77844 p = 1) : d79806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d484 q = 1) (hb : d77844 q = 1) : d79783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d484, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d485 q = 1) (hb : d77844 q = 1) : d79784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d485, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d511 q = 1) (hb : d77844 q = 1) : d79805 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d511, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d512 q = 1) (hb : d77844 q = 1) : d79806 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d512, d79806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d512, d79806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8190 (p : Pattern) (ha : d521 p = 1) (hb : d77844 p = 1) : d79813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d484 q = 1) (hb : d77844 q = 1) : d79783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d484, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d519 q = 1) (hb : d77844 q = 1) : d79811 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d519, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d520 q = 1) (hb : d77844 q = 1) : d79812 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d520, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d521 q = 1) (hb : d77844 q = 1) : d79813 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d521, d79813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d521, d79813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8191 (p : Pattern) (ha : d477 p = 1) (hb : d77842 p = 1) : d7326 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d328 q = 1) : d328 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d475 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d476 q = 1) (hb : d77842 q = 1) : d7325 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d476, d77842, d7325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d476, d77842, d7325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d477 q = 1) (hb : d77842 q = 1) : d7326 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d477, d7326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d477, d7326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro8192 (p : Pattern) (ha : d560 p = 1) (hb : d77844 p = 1) : d79820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d557 q = 1) (hb : d77844 q = 1) : d79817 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d557, d77844, d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d557, d77844, d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d558 q = 1) (hb : d77844 q = 1) : d79818 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d558, d79818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d558, d79818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d559 q = 1) (hb : d77844 q = 1) : d79819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d559, d79819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d559, d79819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d560 q = 1) (hb : d77844 q = 1) : d79820 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d560, d79820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d560, d79820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8193 (p : Pattern) (ha : d69511 p = 1) (hb : d77845 p = 1) : d79827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4789 q = 1) (hb : d77845 q = 1) : d79807 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4789, d77845, d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8189 q ha hb
    | true =>
      simp only [d4789, d77845, d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4790 q = 1) (hb : d77845 q = 1) : d79808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4790, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4790, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4791 q = 1) (hb : d77845 q = 1) : d79809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4791, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4791, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4792 q = 1) (hb : d77845 q = 1) : d79810 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4792, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4792, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4793 q = 1) (hb : d77845 q = 1) : d79814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4793, d77845, d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8190 q ha hb
    | true =>
      simp only [d4793, d77845, d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d4794 q = 1) (hb : d77845 q = 1) : d79815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4794, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4794, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4795 q = 1) (hb : d77845 q = 1) : d79816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4795, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4795, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4796 q = 1) (hb : d77845 q = 1) : d79821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4796, d77845, d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8192 q ha hb
    | true =>
      simp only [d4796, d77845, d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d69507 q = 1) (hb : d77845 q = 1) : d79822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69507, d79822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69507, d79822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d603 q = 1) (hb : d77845 q = 1) : d79787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8183 q ha hb
    | true =>
      simp only [d603, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d604 q = 1) (hb : d77845 q = 1) : d79823 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d79823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d604, d79823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69508 q = 1) (hb : d77845 q = 1) : d79824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69508, d79824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69508, d79824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69509 q = 1) (hb : d77845 q = 1) : d79825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69509, d79825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69509, d79825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69510 q = 1) (hb : d77845 q = 1) : d79826 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69510, d79826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69510, d79826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69511 q = 1) (hb : d77845 q = 1) : d79827 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69511, d79827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69511, d79827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro8194 (p : Pattern) (ha : d609 p = 1) (hb : d77844 p = 1) : d79828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d484 q = 1) (hb : d77844 q = 1) : d79783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d484, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d485 q = 1) (hb : d77844 q = 1) : d79784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d485, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d511 q = 1) (hb : d77844 q = 1) : d79805 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d511, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d609 q = 1) (hb : d77844 q = 1) : d79828 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d609, d79828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d609, d79828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8195 (p : Pattern) (ha : d615 p = 1) (hb : d77844 p = 1) : d79833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d484 q = 1) (hb : d77844 q = 1) : d79783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d484, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d519 q = 1) (hb : d77844 q = 1) : d79811 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d519, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d520 q = 1) (hb : d77844 q = 1) : d79812 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d520, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d615 q = 1) (hb : d77844 q = 1) : d79833 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d615, d79833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d615, d79833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8196 (p : Pattern) (ha : d620 p = 1) (hb : d77844 p = 1) : d79837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d556 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d557 q = 1) (hb : d77844 q = 1) : d79817 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d557, d77844, d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d557, d77844, d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d558 q = 1) (hb : d77844 q = 1) : d79818 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d558, d79818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d558, d79818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d559 q = 1) (hb : d77844 q = 1) : d79819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d559, d79819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d559, d79819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d620 q = 1) (hb : d77844 q = 1) : d79837 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d620, d79837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d620, d79837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro8197 (p : Pattern) (ha : d69516 p = 1) (hb : d77845 p = 1) : d79844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4789 q = 1) (hb : d77845 q = 1) : d79807 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4789, d77845, d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8189 q ha hb
    | true =>
      simp only [d4789, d77845, d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4790 q = 1) (hb : d77845 q = 1) : d79808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4790, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4790, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4791 q = 1) (hb : d77845 q = 1) : d79809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4791, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4791, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4792 q = 1) (hb : d77845 q = 1) : d79810 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4792, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4792, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4793 q = 1) (hb : d77845 q = 1) : d79814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4793, d77845, d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8190 q ha hb
    | true =>
      simp only [d4793, d77845, d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d4794 q = 1) (hb : d77845 q = 1) : d79815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4794, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4794, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4795 q = 1) (hb : d77845 q = 1) : d79816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4795, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4795, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4796 q = 1) (hb : d77845 q = 1) : d79821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4796, d77845, d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8192 q ha hb
    | true =>
      simp only [d4796, d77845, d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d69507 q = 1) (hb : d77845 q = 1) : d79822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69507, d79822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69507, d79822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d603 q = 1) (hb : d77845 q = 1) : d79787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8183 q ha hb
    | true =>
      simp only [d603, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d604 q = 1) (hb : d77845 q = 1) : d79823 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d79823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d604, d79823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69508 q = 1) (hb : d77845 q = 1) : d79824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69508, d79824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69508, d79824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69509 q = 1) (hb : d77845 q = 1) : d79825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69509, d79825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69509, d79825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69510 q = 1) (hb : d77845 q = 1) : d79826 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69510, d79826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69510, d79826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4803 q = 1) (hb : d77845 q = 1) : d79829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4803, d77845, d79829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8194 q ha hb
    | true =>
      simp only [d4803, d77845, d79829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d4804 q = 1) (hb : d77845 q = 1) : d79830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4804, d79830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4804, d79830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4805 q = 1) (hb : d77845 q = 1) : d79831 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4805, d79831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4805, d79831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4806 q = 1) (hb : d77845 q = 1) : d79832 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4806, d79832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4806, d79832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d4807 q = 1) (hb : d77845 q = 1) : d79834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4807, d77845, d79834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8195 q ha hb
    | true =>
      simp only [d4807, d77845, d79834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d4808 q = 1) (hb : d77845 q = 1) : d79835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4808, d79835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4808, d79835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d4809 q = 1) (hb : d77845 q = 1) : d79836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4809, d79836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4809, d79836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d4810 q = 1) (hb : d77845 q = 1) : d79838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4810, d77845, d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8196 q ha hb
    | true =>
      simp only [d4810, d77845, d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d69512 q = 1) (hb : d77845 q = 1) : d79839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69512, d79839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d69512, d79839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d626 q = 1) (hb : d77845 q = 1) : d79796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d77845, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8185 q ha hb
    | true =>
      simp only [d626, d77845, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d627 q = 1) (hb : d77845 q = 1) : d79840 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d79840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d627, d79840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d69513 q = 1) (hb : d77845 q = 1) : d79841 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69513, d79841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69513, d79841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d69514 q = 1) (hb : d77845 q = 1) : d79842 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69514, d79842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d69514, d79842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d69515 q = 1) (hb : d77845 q = 1) : d79843 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69515, d79843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d69515, d79843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d69516 q = 1) (hb : d77845 q = 1) : d79844 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69516, d79844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69516, d79844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  exact h30 p ha hb
theorem andIntro8198 (p : Pattern) (ha : d69523 p = 1) (hb : d77845 p = 1) : d79851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4810 q = 1) (hb : d77845 q = 1) : d79838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4810, d77845, d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8196 q ha hb
    | true =>
      simp only [d4810, d77845, d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69512 q = 1) (hb : d77845 q = 1) : d79839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69512, d79839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69512, d79839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d626 q = 1) (hb : d77845 q = 1) : d79796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d77845, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8185 q ha hb
    | true =>
      simp only [d626, d77845, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d627 q = 1) (hb : d77845 q = 1) : d79840 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d79840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d627, d79840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69513 q = 1) (hb : d77845 q = 1) : d79841 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69513, d79841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69513, d79841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69521 q = 1) (hb : d77845 q = 1) : d79849 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69521, d79849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69521, d79849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69522 q = 1) (hb : d77845 q = 1) : d79850 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69522, d79850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69522, d79850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69523 q = 1) (hb : d77845 q = 1) : d79851 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69523, d79851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69523, d79851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8199 (p : Pattern) (ha : d675 p = 1) (hb : d77842 p = 1) : d7390 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d421 q = 1) : d421 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d673 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d674 q = 1) (hb : d77842 q = 1) : d7389 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d674, d77842, d7389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d674, d77842, d7389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d675 q = 1) (hb : d77842 q = 1) : d7390 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d675, d7390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d675, d7390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro8200 (p : Pattern) (ha : d681 p = 1) (hb : d77844 p = 1) : d79860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d676 q = 1) (hb : d77842 q = 1) : d7391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8199 q ha hb
    | true =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d677 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d678 q = 1) (hb : d77844 q = 1) : d79857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d678, d77844, d79857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d678, d77844, d79857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d679 q = 1) (hb : d77844 q = 1) : d79858 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d679, d79858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d679, d79858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d680 q = 1) (hb : d77844 q = 1) : d79859 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d680, d79859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d680, d79859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d681 q = 1) (hb : d77844 q = 1) : d79860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d681, d79860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d681, d79860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro8201 (p : Pattern) (ha : d689 p = 1) (hb : d77844 p = 1) : d79866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d677 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d685 q = 1) (hb : d77842 q = 1) : d685 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d686 q = 1) (hb : d77844 q = 1) : d79863 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d686, d77844, d79863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d686, d77844, d79863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d687 q = 1) (hb : d77844 q = 1) : d79864 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d687, d79864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d687, d79864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d688 q = 1) (hb : d77844 q = 1) : d79865 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d688, d79865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d688, d79865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d689 q = 1) (hb : d77844 q = 1) : d79866 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d689, d79866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d689, d79866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8202 (p : Pattern) (ha : d69533 p = 1) (hb : d77845 p = 1) : d79872 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4849 q = 1) (hb : d77845 q = 1) : d79861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4849, d77845, d79861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8200 q ha hb
    | true =>
      simp only [d4849, d77845, d79861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69529 q = 1) (hb : d77845 q = 1) : d79862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69529, d79862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69529, d79862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d720 q = 1) (hb : d77845 q = 1) : d79867 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d720, d77845, d79867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8201 q ha hb
    | true =>
      simp only [d720, d77845, d79867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d721 q = 1) (hb : d77845 q = 1) : d79868 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d721, d79868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d721, d79868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69530 q = 1) (hb : d77845 q = 1) : d79869 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69530, d79869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69530, d79869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69531 q = 1) (hb : d77845 q = 1) : d79870 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69531, d79870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69531, d79870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69532 q = 1) (hb : d77845 q = 1) : d79871 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69532, d79871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69532, d79871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69533 q = 1) (hb : d77845 q = 1) : d79872 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69533, d79872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69533, d79872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8203 (p : Pattern) (ha : d70007 p = 1) (hb : d77845 p = 1) : d79878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4779 q = 1) (hb : d77845 q = 1) : d79793 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4779, d79793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4779, d79793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8184 q ha hb
  have h2 (q : Pattern) (ha : d4780 q = 1) (hb : d77845 q = 1) : d79794 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4780, d79794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4780, d79794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4786 q = 1) (hb : d77845 q = 1) : d79802 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4786, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8184 q ha hb
    | true =>
      simp only [d4786, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8186 q ha hb
  have h4 (q : Pattern) (ha : d4787 q = 1) (hb : d77845 q = 1) : d79803 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4787, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4787, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4788 q = 1) (hb : d77845 q = 1) : d79804 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4788, d79804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4788, d79804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69517 q = 1) (hb : d77845 q = 1) : d79845 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69517, d79845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8193 q ha hb
    | true =>
      simp only [d69517, d79845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8197 q ha hb
  have h7 (q : Pattern) (ha : d4837 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8188 q ha hb
    | true =>
      simp only [d4837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8179 q ha hb
  have h8 (q : Pattern) (ha : d69996 q = 1) (hb : d77845 q = 1) : d79846 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69996, d79846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69996, d79846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69997 q = 1) (hb : d77845 q = 1) : d79847 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69997, d79847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69997, d79847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d69998 q = 1) (hb : d77845 q = 1) : d79848 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69998, d79848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69998, d79848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69524 q = 1) (hb : d77845 q = 1) : d79852 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69524, d79852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69524, d79852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8198 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8180 q ha hb
  have h13 (q : Pattern) (ha : d69999 q = 1) (hb : d77845 q = 1) : d79853 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69999, d79853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69999, d79853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70000 q = 1) (hb : d77845 q = 1) : d79854 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70000, d79854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70000, d79854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d70001 q = 1) (hb : d77845 q = 1) : d79855 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70001, d79855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70001, d79855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d70002 q = 1) (hb : d77845 q = 1) : d79856 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70002, d79856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70002, d79856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69534 q = 1) (hb : d77845 q = 1) : d79873 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69534, d79873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69534, d79873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8202 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8182 q ha hb
  have h19 (q : Pattern) (ha : d70003 q = 1) (hb : d77845 q = 1) : d79874 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70003, d79874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70003, d79874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70004 q = 1) (hb : d77845 q = 1) : d79875 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70004, d79875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d70004, d79875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d70005 q = 1) (hb : d77845 q = 1) : d79876 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70005, d79876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d70005, d79876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d70006 q = 1) (hb : d77845 q = 1) : d79877 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70006, d79877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d70006, d79877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d70007 q = 1) (hb : d77845 q = 1) : d79878 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70007, d79878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70007, d79878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro8204 (p : Pattern) (ha : d70013 p = 1) (hb : d77845 p = 1) : d79884 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70008 q = 1) (hb : d77845 q = 1) : d79879 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70008, d79879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70008, d79879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8203 q ha hb
  have h2 (q : Pattern) (ha : d70009 q = 1) (hb : d77845 q = 1) : d79880 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70009, d79880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70009, d79880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70010 q = 1) (hb : d77845 q = 1) : d79881 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70010, d79881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70010, d79881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70011 q = 1) (hb : d77845 q = 1) : d79882 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70011, d79882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70011, d79882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70012 q = 1) (hb : d77845 q = 1) : d79883 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70012, d79883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70012, d79883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70013 q = 1) (hb : d77845 q = 1) : d79884 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70013, d79884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70013, d79884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8205 (p : Pattern) (ha : d783 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d780, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8206 (p : Pattern) (ha : d793 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d780 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d780, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8207 (p : Pattern) (ha : d950 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d939 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8205 q ha hb
    | true =>
      simp only [d939, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d940 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d941 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d942 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d943 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d945 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8206 q ha hb
    | true =>
      simp only [d945, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d946 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d947 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d948 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d949 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d950 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8208 (p : Pattern) (ha : d959 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d945 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8206 q ha hb
    | true =>
      simp only [d945, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d946 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d947 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d948 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d949 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d959 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8209 (p : Pattern) (ha : d1063 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1007 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1060 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1060, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8210 (p : Pattern) (ha : d1069 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1064 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8209 q ha hb
    | true =>
      simp only [d1064, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1065 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1066 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1067 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1068 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1069 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8211 (p : Pattern) (ha : d779 p = 1) (hb : d77844 p = 1) : d79889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d771 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d776 q = 1) (hb : d77844 q = 1) : d79886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d776, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d777 q = 1) (hb : d77844 q = 1) : d79887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d777, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d778 q = 1) (hb : d77844 q = 1) : d79888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d778, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d778, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d779 q = 1) (hb : d77844 q = 1) : d79889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d779, d79889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d779, d79889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8212 (p : Pattern) (ha : d4873 p = 1) (hb : d77845 p = 1) : d79895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d909 q = 1) (hb : d77845 q = 1) : d79890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8211 q ha hb
    | true =>
      simp only [d909, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4869 q = 1) (hb : d77845 q = 1) : d79891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4869, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4869, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4870 q = 1) (hb : d77845 q = 1) : d79892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4870, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4870, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4871 q = 1) (hb : d77845 q = 1) : d79893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4871, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4871, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4872 q = 1) (hb : d77845 q = 1) : d79894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4872, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4872, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4873 q = 1) (hb : d77845 q = 1) : d79895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4873, d79895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4873, d79895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8213 (p : Pattern) (ha : d792 p = 1) (hb : d77844 p = 1) : d79898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d771 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d776 q = 1) (hb : d77844 q = 1) : d79886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d776, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d777 q = 1) (hb : d77844 q = 1) : d79887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d777, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d778 q = 1) (hb : d77844 q = 1) : d79888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d778, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d778, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d792 q = 1) (hb : d77844 q = 1) : d79898 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d792, d79898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d792, d79898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8214 (p : Pattern) (ha : d4880 p = 1) (hb : d77845 p = 1) : d79904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d909 q = 1) (hb : d77845 q = 1) : d79890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8211 q ha hb
    | true =>
      simp only [d909, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4869 q = 1) (hb : d77845 q = 1) : d79891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4869, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4869, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4870 q = 1) (hb : d77845 q = 1) : d79892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4870, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4870, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4871 q = 1) (hb : d77845 q = 1) : d79893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4871, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4871, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4872 q = 1) (hb : d77845 q = 1) : d79894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4872, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4872, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d932 q = 1) (hb : d77845 q = 1) : d79899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d77845, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8213 q ha hb
    | true =>
      simp only [d932, d77845, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d4876 q = 1) (hb : d77845 q = 1) : d79900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4876, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4876, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4877 q = 1) (hb : d77845 q = 1) : d79901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4877, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4877, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4878 q = 1) (hb : d77845 q = 1) : d79902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4878, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4878, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4879 q = 1) (hb : d77845 q = 1) : d79903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4879, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4879, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4880 q = 1) (hb : d77845 q = 1) : d79904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4880, d79904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4880, d79904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8215 (p : Pattern) (ha : d4925 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4921 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4922 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4922, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4922, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4923 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4924 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4925 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8216 (p : Pattern) (ha : d4931 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4926 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4926, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8215 q ha hb
    | true =>
      simp only [d4926, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4927 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4928 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4929 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4930 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d939 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8205 q ha hb
    | true =>
      simp only [d939, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d940 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d941 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d942 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d943 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4931 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8217 (p : Pattern) (ha : d804 p = 1) (hb : d77844 p = 1) : d79909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d771 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d776 q = 1) (hb : d77844 q = 1) : d79886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d776, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d777 q = 1) (hb : d77844 q = 1) : d79887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d777, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d803 q = 1) (hb : d77844 q = 1) : d79908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d803, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d804 q = 1) (hb : d77844 q = 1) : d79909 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d804, d79909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d804, d79909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8218 (p : Pattern) (ha : d813 p = 1) (hb : d77844 p = 1) : d79916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d771 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d776 q = 1) (hb : d77844 q = 1) : d79886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d776, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d811 q = 1) (hb : d77844 q = 1) : d79914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d812 q = 1) (hb : d77844 q = 1) : d79915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d812, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d813 q = 1) (hb : d77844 q = 1) : d79916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d813, d79916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d813, d79916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8219 (p : Pattern) (ha : d769 p = 1) (hb : d77842 p = 1) : d7575 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d766 q = 1) : d766 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d767 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d768 q = 1) (hb : d77842 q = 1) : d7574 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d768, d77842, d7574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d768, d77842, d7574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d769 q = 1) (hb : d77842 q = 1) : d7575 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d769, d7575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d769, d7575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro8220 (p : Pattern) (ha : d851 p = 1) (hb : d77844 p = 1) : d79923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d847 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d848 q = 1) (hb : d77844 q = 1) : d79920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d848, d77844, d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d848, d77844, d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d849 q = 1) (hb : d77844 q = 1) : d79921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d849, d79921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d849, d79921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d850 q = 1) (hb : d77844 q = 1) : d79922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d850, d79922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d850, d79922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d851 q = 1) (hb : d77844 q = 1) : d79923 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d851, d79923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d851, d79923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8221 (p : Pattern) (ha : d69551 p = 1) (hb : d77845 p = 1) : d79930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4884 q = 1) (hb : d77845 q = 1) : d79910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4884, d77845, d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8217 q ha hb
    | true =>
      simp only [d4884, d77845, d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4885 q = 1) (hb : d77845 q = 1) : d79911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4885, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4885, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4886 q = 1) (hb : d77845 q = 1) : d79912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4886, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4886, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4887 q = 1) (hb : d77845 q = 1) : d79913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4887, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4887, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4888 q = 1) (hb : d77845 q = 1) : d79917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4888, d77845, d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8218 q ha hb
    | true =>
      simp only [d4888, d77845, d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d4889 q = 1) (hb : d77845 q = 1) : d79918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4889, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4889, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4890 q = 1) (hb : d77845 q = 1) : d79919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4890, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4890, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4891 q = 1) (hb : d77845 q = 1) : d79924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4891, d77845, d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8220 q ha hb
    | true =>
      simp only [d4891, d77845, d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d69547 q = 1) (hb : d77845 q = 1) : d79925 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69547, d79925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69547, d79925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d909 q = 1) (hb : d77845 q = 1) : d79890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8211 q ha hb
    | true =>
      simp only [d909, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d910 q = 1) (hb : d77845 q = 1) : d79926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d79926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d910, d79926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69548 q = 1) (hb : d77845 q = 1) : d79927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69548, d79927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69548, d79927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69549 q = 1) (hb : d77845 q = 1) : d79928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69549, d79928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69549, d79928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69550 q = 1) (hb : d77845 q = 1) : d79929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69550, d79929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69550, d79929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69551 q = 1) (hb : d77845 q = 1) : d79930 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69551, d79930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69551, d79930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro8222 (p : Pattern) (ha : d915 p = 1) (hb : d77844 p = 1) : d79931 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d771 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d776 q = 1) (hb : d77844 q = 1) : d79886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d776, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d777 q = 1) (hb : d77844 q = 1) : d79887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d777, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d803 q = 1) (hb : d77844 q = 1) : d79908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d803, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d915 q = 1) (hb : d77844 q = 1) : d79931 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d915, d79931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d915, d79931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8223 (p : Pattern) (ha : d921 p = 1) (hb : d77844 p = 1) : d79936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d771 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d776 q = 1) (hb : d77844 q = 1) : d79886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d776, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d811 q = 1) (hb : d77844 q = 1) : d79914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d812 q = 1) (hb : d77844 q = 1) : d79915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d812, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d921 q = 1) (hb : d77844 q = 1) : d79936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d921, d79936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d921, d79936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro8224 (p : Pattern) (ha : d926 p = 1) (hb : d77844 p = 1) : d79940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d847 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d848 q = 1) (hb : d77844 q = 1) : d79920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d848, d77844, d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d848, d77844, d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d849 q = 1) (hb : d77844 q = 1) : d79921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d849, d79921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d849, d79921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d850 q = 1) (hb : d77844 q = 1) : d79922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d850, d79922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d850, d79922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d926 q = 1) (hb : d77844 q = 1) : d79940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d926, d79940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d926, d79940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro8225 (p : Pattern) (ha : d69556 p = 1) (hb : d77845 p = 1) : d79947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4884 q = 1) (hb : d77845 q = 1) : d79910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4884, d77845, d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8217 q ha hb
    | true =>
      simp only [d4884, d77845, d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4885 q = 1) (hb : d77845 q = 1) : d79911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4885, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4885, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4886 q = 1) (hb : d77845 q = 1) : d79912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4886, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4886, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4887 q = 1) (hb : d77845 q = 1) : d79913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4887, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4887, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4888 q = 1) (hb : d77845 q = 1) : d79917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4888, d77845, d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8218 q ha hb
    | true =>
      simp only [d4888, d77845, d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d4889 q = 1) (hb : d77845 q = 1) : d79918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4889, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4889, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4890 q = 1) (hb : d77845 q = 1) : d79919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4890, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4890, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4891 q = 1) (hb : d77845 q = 1) : d79924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4891, d77845, d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8220 q ha hb
    | true =>
      simp only [d4891, d77845, d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d69547 q = 1) (hb : d77845 q = 1) : d79925 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69547, d79925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69547, d79925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d909 q = 1) (hb : d77845 q = 1) : d79890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8211 q ha hb
    | true =>
      simp only [d909, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d910 q = 1) (hb : d77845 q = 1) : d79926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d79926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d910, d79926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69548 q = 1) (hb : d77845 q = 1) : d79927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69548, d79927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69548, d79927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69549 q = 1) (hb : d77845 q = 1) : d79928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69549, d79928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69549, d79928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69550 q = 1) (hb : d77845 q = 1) : d79929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69550, d79929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69550, d79929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4898 q = 1) (hb : d77845 q = 1) : d79932 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4898, d77845, d79932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8222 q ha hb
    | true =>
      simp only [d4898, d77845, d79932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d4899 q = 1) (hb : d77845 q = 1) : d79933 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4899, d79933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4899, d79933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4900 q = 1) (hb : d77845 q = 1) : d79934 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4900, d79934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4900, d79934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4901 q = 1) (hb : d77845 q = 1) : d79935 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4901, d79935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4901, d79935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d4902 q = 1) (hb : d77845 q = 1) : d79937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4902, d77845, d79937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8223 q ha hb
    | true =>
      simp only [d4902, d77845, d79937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d4903 q = 1) (hb : d77845 q = 1) : d79938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4903, d79938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4903, d79938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d4904 q = 1) (hb : d77845 q = 1) : d79939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4904, d79939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4904, d79939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d4905 q = 1) (hb : d77845 q = 1) : d79941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4905, d77845, d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8224 q ha hb
    | true =>
      simp only [d4905, d77845, d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d69552 q = 1) (hb : d77845 q = 1) : d79942 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69552, d79942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d69552, d79942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d932 q = 1) (hb : d77845 q = 1) : d79899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d77845, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8213 q ha hb
    | true =>
      simp only [d932, d77845, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d933 q = 1) (hb : d77845 q = 1) : d79943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d79943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d933, d79943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d69553 q = 1) (hb : d77845 q = 1) : d79944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69553, d79944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69553, d79944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d69554 q = 1) (hb : d77845 q = 1) : d79945 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69554, d79945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d69554, d79945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d69555 q = 1) (hb : d77845 q = 1) : d79946 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69555, d79946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d69555, d79946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d69556 q = 1) (hb : d77845 q = 1) : d79947 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69556, d79947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69556, d79947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  exact h30 p ha hb
theorem andIntro8226 (p : Pattern) (ha : d69563 p = 1) (hb : d77845 p = 1) : d79954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4905 q = 1) (hb : d77845 q = 1) : d79941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4905, d77845, d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8224 q ha hb
    | true =>
      simp only [d4905, d77845, d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69552 q = 1) (hb : d77845 q = 1) : d79942 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69552, d79942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69552, d79942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d932 q = 1) (hb : d77845 q = 1) : d79899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d77845, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8213 q ha hb
    | true =>
      simp only [d932, d77845, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d933 q = 1) (hb : d77845 q = 1) : d79943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d79943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d933, d79943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69553 q = 1) (hb : d77845 q = 1) : d79944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69553, d79944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69553, d79944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69561 q = 1) (hb : d77845 q = 1) : d79952 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69561, d79952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69561, d79952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69562 q = 1) (hb : d77845 q = 1) : d79953 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69562, d79953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69562, d79953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69563 q = 1) (hb : d77845 q = 1) : d79954 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69563, d79954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69563, d79954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8227 (p : Pattern) (ha : d997 p = 1) (hb : d77842 p = 1) : d7681 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d990 q = 1) : d990 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d996 q = 1) (hb : d77842 q = 1) : d7680 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d996, d77842, d7680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d996, d77842, d7680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d997 q = 1) (hb : d77842 q = 1) : d7681 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d997, d7681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d997, d7681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro8228 (p : Pattern) (ha : d1003 p = 1) (hb : d77844 p = 1) : d79963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d994 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d998 q = 1) (hb : d77842 q = 1) : d7682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d7682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8227 q ha hb
    | true =>
      simp only [d998, d7682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d999 q = 1) (hb : d77842 q = 1) : d7683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d7683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d999, d7683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1000 q = 1) (hb : d77844 q = 1) : d79960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1000, d77844, d79960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1000, d77844, d79960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1001 q = 1) (hb : d77844 q = 1) : d79961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1001, d79961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1001, d79961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1002 q = 1) (hb : d77844 q = 1) : d79962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1002, d79962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1002, d79962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1003 q = 1) (hb : d77844 q = 1) : d79963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1003, d79963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1003, d79963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro8229 (p : Pattern) (ha : d1011 p = 1) (hb : d77844 p = 1) : d79969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d999 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1007 q = 1) (hb : d77842 q = 1) : d1007 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1008 q = 1) (hb : d77844 q = 1) : d79966 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1008, d77844, d79966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1008, d77844, d79966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1009 q = 1) (hb : d77844 q = 1) : d79967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1009, d79967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1009, d79967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1010 q = 1) (hb : d77844 q = 1) : d79968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1010, d79968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1010, d79968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1011 q = 1) (hb : d77844 q = 1) : d79969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1011, d79969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1011, d79969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8230 (p : Pattern) (ha : d69573 p = 1) (hb : d77845 p = 1) : d79975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4944 q = 1) (hb : d77845 q = 1) : d79964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4944, d77845, d79964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8228 q ha hb
    | true =>
      simp only [d4944, d77845, d79964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69569 q = 1) (hb : d77845 q = 1) : d79965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69569, d79965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69569, d79965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1053 q = 1) (hb : d77845 q = 1) : d79970 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1053, d77845, d79970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8229 q ha hb
    | true =>
      simp only [d1053, d77845, d79970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1054 q = 1) (hb : d77845 q = 1) : d79971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1054, d79971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1054, d79971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69570 q = 1) (hb : d77845 q = 1) : d79972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69570, d79972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69570, d79972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69571 q = 1) (hb : d77845 q = 1) : d79973 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69571, d79973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69571, d79973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69572 q = 1) (hb : d77845 q = 1) : d79974 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69572, d79974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69572, d79974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69573 q = 1) (hb : d77845 q = 1) : d79975 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69573, d79975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69573, d79975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro8231 (p : Pattern) (ha : d70026 p = 1) (hb : d77845 p = 1) : d79981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4874 q = 1) (hb : d77845 q = 1) : d79896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4874, d79896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4874, d79896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8212 q ha hb
  have h2 (q : Pattern) (ha : d4875 q = 1) (hb : d77845 q = 1) : d79897 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4875, d79897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4875, d79897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4881 q = 1) (hb : d77845 q = 1) : d79905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4881, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8212 q ha hb
    | true =>
      simp only [d4881, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8214 q ha hb
  have h4 (q : Pattern) (ha : d4882 q = 1) (hb : d77845 q = 1) : d79906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4882, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4882, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4883 q = 1) (hb : d77845 q = 1) : d79907 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4883, d79907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4883, d79907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69557 q = 1) (hb : d77845 q = 1) : d79948 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69557, d79948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8221 q ha hb
    | true =>
      simp only [d69557, d79948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8225 q ha hb
  have h7 (q : Pattern) (ha : d4932 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8216 q ha hb
    | true =>
      simp only [d4932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8207 q ha hb
  have h8 (q : Pattern) (ha : d70015 q = 1) (hb : d77845 q = 1) : d79949 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70015, d79949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70015, d79949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70016 q = 1) (hb : d77845 q = 1) : d79950 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70016, d79950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70016, d79950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d70017 q = 1) (hb : d77845 q = 1) : d79951 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70017, d79951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70017, d79951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69564 q = 1) (hb : d77845 q = 1) : d79955 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69564, d79955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69564, d79955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8226 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8208 q ha hb
  have h13 (q : Pattern) (ha : d70018 q = 1) (hb : d77845 q = 1) : d79956 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70018, d79956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70018, d79956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70019 q = 1) (hb : d77845 q = 1) : d79957 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70019, d79957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70019, d79957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d70020 q = 1) (hb : d77845 q = 1) : d79958 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70020, d79958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70020, d79958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d70021 q = 1) (hb : d77845 q = 1) : d79959 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70021, d79959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70021, d79959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69574 q = 1) (hb : d77845 q = 1) : d79976 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69574, d79976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69574, d79976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8230 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8210 q ha hb
  have h19 (q : Pattern) (ha : d70022 q = 1) (hb : d77845 q = 1) : d79977 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70022, d79977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d70022, d79977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70023 q = 1) (hb : d77845 q = 1) : d79978 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70023, d79978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d70023, d79978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d70024 q = 1) (hb : d77845 q = 1) : d79979 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70024, d79979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d70024, d79979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d70025 q = 1) (hb : d77845 q = 1) : d79980 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70025, d79980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d70025, d79980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d70026 q = 1) (hb : d77845 q = 1) : d79981 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70026, d79981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d70026, d79981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro8232 (p : Pattern) (ha : d70032 p = 1) (hb : d77845 p = 1) : d79987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70027 q = 1) (hb : d77845 q = 1) : d79982 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70027, d79982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70027, d79982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8231 q ha hb
  have h2 (q : Pattern) (ha : d70028 q = 1) (hb : d77845 q = 1) : d79983 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70028, d79983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70028, d79983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70029 q = 1) (hb : d77845 q = 1) : d79984 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70029, d79984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70029, d79984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70030 q = 1) (hb : d77845 q = 1) : d79985 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70030, d79985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70030, d79985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70031 q = 1) (hb : d77845 q = 1) : d79986 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70031, d79986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70031, d79986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70032 q = 1) (hb : d77845 q = 1) : d79987 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70032, d79987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d70032, d79987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8233 (p : Pattern) (ha : d1162 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1159, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1162 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8234 (p : Pattern) (ha : d1172 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1159 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1159, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1172 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8235 (p : Pattern) (ha : d1361 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1350 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8233 q ha hb
    | true =>
      simp only [d1350, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1351 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1352 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1353 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1354 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1356 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8234 q ha hb
    | true =>
      simp only [d1356, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1357 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1358 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1359 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1360 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1361 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8236 (p : Pattern) (ha : d1370 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1356 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8234 q ha hb
    | true =>
      simp only [d1356, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1357 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1358 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1359 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1360 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1370 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8237 (p : Pattern) (ha : d1497 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1494 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1494, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1495 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1496 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1497 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8238 (p : Pattern) (ha : d1503 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1498 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8237 q ha hb
    | true =>
      simp only [d1498, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1499 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1500 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1501 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1502 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1503 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8239 (p : Pattern) (ha : d1158 p = 1) (hb : d77844 p = 1) : d79993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1150 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d77842 q = 1) : d1154 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1155 q = 1) (hb : d77844 q = 1) : d79990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1155, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1156 q = 1) (hb : d77844 q = 1) : d79991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1156, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1157 q = 1) (hb : d77844 q = 1) : d79992 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1157, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1158 q = 1) (hb : d77844 q = 1) : d79993 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1158, d79993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1158, d79993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8240 (p : Pattern) (ha : d4969 p = 1) (hb : d77845 p = 1) : d79999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1320 q = 1) (hb : d77845 q = 1) : d79994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8239 q ha hb
    | true =>
      simp only [d1320, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4965 q = 1) (hb : d77845 q = 1) : d79995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4965, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4965, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4966 q = 1) (hb : d77845 q = 1) : d79996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4966, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4966, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4967 q = 1) (hb : d77845 q = 1) : d79997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4967, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4967, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4968 q = 1) (hb : d77845 q = 1) : d79998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4968, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4968, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4969 q = 1) (hb : d77845 q = 1) : d79999 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4969, d79999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4969, d79999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro8241 (p : Pattern) (ha : d1171 p = 1) (hb : d77844 p = 1) : d80002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1154 q = 1) (hb : d77842 q = 1) : d1154 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1155 q = 1) (hb : d77844 q = 1) : d79990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1155, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1156 q = 1) (hb : d77844 q = 1) : d79991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1156, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1157 q = 1) (hb : d77844 q = 1) : d79992 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1157, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d1171 q = 1) (hb : d77844 q = 1) : d80002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1171, d80002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1171, d80002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro8242 (p : Pattern) (ha : d4976 p = 1) (hb : d77845 p = 1) : d80008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1320 q = 1) (hb : d77845 q = 1) : d79994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8239 q ha hb
    | true =>
      simp only [d1320, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4965 q = 1) (hb : d77845 q = 1) : d79995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4965, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4965, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4966 q = 1) (hb : d77845 q = 1) : d79996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4966, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4966, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4967 q = 1) (hb : d77845 q = 1) : d79997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4967, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4967, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4968 q = 1) (hb : d77845 q = 1) : d79998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4968, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4968, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1343 q = 1) (hb : d77845 q = 1) : d80003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d77845, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8241 q ha hb
    | true =>
      simp only [d1343, d77845, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d4972 q = 1) (hb : d77845 q = 1) : d80004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4972, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4972, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4973 q = 1) (hb : d77845 q = 1) : d80005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4973, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4973, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4974 q = 1) (hb : d77845 q = 1) : d80006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4974, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4974, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4975 q = 1) (hb : d77845 q = 1) : d80007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4975, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4975, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4976 q = 1) (hb : d77845 q = 1) : d80008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4976, d80008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4976, d80008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8243 (p : Pattern) (ha : d5035 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5031 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5032 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5032, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d5032, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5033 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5034 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5035 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8244 (p : Pattern) (ha : d5041 p = 1) (hb : d77845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5036 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5036, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8243 q ha hb
    | true =>
      simp only [d5036, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5037 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5038 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5039 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5040 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1350 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8233 q ha hb
    | true =>
      simp only [d1350, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1351 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1352 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1353 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1354 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5041 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro8245 (p : Pattern) (ha : d1183 p = 1) (hb : d77844 p = 1) : d80013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1150 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d77842 q = 1) : d1154 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1155 q = 1) (hb : d77844 q = 1) : d79990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1155, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1156 q = 1) (hb : d77844 q = 1) : d79991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1156, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1182 q = 1) (hb : d77844 q = 1) : d80012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1183 q = 1) (hb : d77844 q = 1) : d80013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1183, d80013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1183, d80013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8246 (p : Pattern) (ha : d1192 p = 1) (hb : d77844 p = 1) : d80020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1150 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d77842 q = 1) : d1154 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1155 q = 1) (hb : d77844 q = 1) : d79990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1155, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1190 q = 1) (hb : d77844 q = 1) : d80018 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1191 q = 1) (hb : d77844 q = 1) : d80019 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1191, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1192 q = 1) (hb : d77844 q = 1) : d80020 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1192, d80020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1192, d80020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro8247 (p : Pattern) (ha : d1148 p = 1) (hb : d77842 p = 1) : d7728 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1145 q = 1) : d1145 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1147 q = 1) (hb : d77842 q = 1) : d7727 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1147, d77842, d7727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1147, d77842, d7727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1148 q = 1) (hb : d77842 q = 1) : d7728 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1148, d7728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1148, d7728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro8248 (p : Pattern) (ha : d1227 p = 1) (hb : d77844 p = 1) : d80027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1223 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1224 q = 1) (hb : d77844 q = 1) : d80024 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1224, d77844, d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1224, d77844, d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1225 q = 1) (hb : d77844 q = 1) : d80025 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1225, d80025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1225, d80025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1226 q = 1) (hb : d77844 q = 1) : d80026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1226, d80026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1226, d80026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1227 q = 1) (hb : d77844 q = 1) : d80027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1227, d80027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1227, d80027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro8249 (p : Pattern) (ha : d69592 p = 1) (hb : d77845 p = 1) : d80034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4980 q = 1) (hb : d77845 q = 1) : d80014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4980, d77845, d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8245 q ha hb
    | true =>
      simp only [d4980, d77845, d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4981 q = 1) (hb : d77845 q = 1) : d80015 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4981, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4981, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4982 q = 1) (hb : d77845 q = 1) : d80016 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4982, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4982, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4983 q = 1) (hb : d77845 q = 1) : d80017 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4983, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4983, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4984 q = 1) (hb : d77845 q = 1) : d80021 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4984, d77845, d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8246 q ha hb
    | true =>
      simp only [d4984, d77845, d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d4985 q = 1) (hb : d77845 q = 1) : d80022 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4985, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4985, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4986 q = 1) (hb : d77845 q = 1) : d80023 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4986, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4986, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4987 q = 1) (hb : d77845 q = 1) : d80028 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4987, d77845, d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8248 q ha hb
    | true =>
      simp only [d4987, d77845, d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d69588 q = 1) (hb : d77845 q = 1) : d80029 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69588, d80029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69588, d80029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1320 q = 1) (hb : d77845 q = 1) : d79994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8239 q ha hb
    | true =>
      simp only [d1320, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1321 q = 1) (hb : d77845 q = 1) : d80030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d80030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1321, d80030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69589 q = 1) (hb : d77845 q = 1) : d80031 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69589, d80031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69589, d80031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69590 q = 1) (hb : d77845 q = 1) : d80032 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69590, d80032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69590, d80032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69591 q = 1) (hb : d77845 q = 1) : d80033 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69591, d80033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69591, d80033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69592 q = 1) (hb : d77845 q = 1) : d80034 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69592, d80034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69592, d80034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
end NetHack.Soko22Hazard87
