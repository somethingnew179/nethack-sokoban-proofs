import NetHack.Soko22Hazard87.AndIntroBlocks0070
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro17750 (p : Pattern) (ha : d92756 p = 1) (hb : d112535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92736 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92745 q = 1) (hb : d112530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92745, d112530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17749 q ha hb
    | true =>
      simp only [d92745, d112530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro118 q hb ha
  have h3 (q : Pattern) (ha : d92746 q = 1) (hb : d112531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92746, d112531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92746, d112531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92752 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92753 q = 1) (hb : d112532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92753, d112532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92753, d112532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92754 q = 1) (hb : d112533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92754, d112533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92754, d112533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92755 q = 1) (hb : d112534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92755, d112534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92755, d112534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92756 q = 1) (hb : d112535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92756, d112535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92756, d112535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17751 (p : Pattern) (ha : d92762 p = 1) (hb : d112541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92646 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92704 q = 1) (hb : d111940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92704, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17746 q ha hb
    | true =>
      simp only [d92704, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17747 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92711 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92712 q = 1) (hb : d111941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92712, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92712, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92713 q = 1) (hb : d112522 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92713, d112522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92713, d112522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92714 q = 1) (hb : d112523 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92714, d112523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92714, d112523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92718 q = 1) (hb : d112525 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92718, d112525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92718, d112525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17748 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d92719 q = 1) (hb : d112526 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92719, d112526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92719, d112526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92720 q = 1) (hb : d112527 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92720, d112527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92720, d112527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92721 q = 1) (hb : d112528 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92721, d112528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92721, d112528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d92722 q = 1) (hb : d112529 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92722, d112529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92722, d112529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92757 q = 1) (hb : d112536 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92757, d112536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92757, d112536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17750 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92758 q = 1) (hb : d112537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92758, d112537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92758, d112537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92759 q = 1) (hb : d112538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92759, d112538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92759, d112538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92760 q = 1) (hb : d112539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92760, d112539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92760, d112539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d92761 q = 1) (hb : d112540 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92761, d112540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92761, d112540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d92762 q = 1) (hb : d112541 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92762, d112541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92762, d112541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17752 (p : Pattern) (ha : d92768 p = 1) (hb : d112547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92763 q = 1) (hb : d112542 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92763, d112542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92763, d112542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17751 q ha hb
  have h2 (q : Pattern) (ha : d92764 q = 1) (hb : d112543 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92764, d112543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92764, d112543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92765 q = 1) (hb : d112544 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92765, d112544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92765, d112544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92766 q = 1) (hb : d112545 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92766, d112545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92766, d112545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92767 q = 1) (hb : d112546 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92767, d112546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92767, d112546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92768 q = 1) (hb : d112547 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92768, d112547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92768, d112547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17753 (p : Pattern) (ha : d92833 p = 1) (hb : d112055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92802 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92808 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92822 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92779 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92779, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17604 q ha hb
    | true =>
      simp only [d92779, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h5 (q : Pattern) (ha : d92823 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92823, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92823, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92829 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92830 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92830, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92830, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92831 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92831, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92831, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92832 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92832, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92832, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92833 q = 1) (hb : d112055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92833, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92833, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17754 (p : Pattern) (ha : d92853 p = 1) (hb : d112064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92808 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92822 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92779 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92779, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17604 q ha hb
    | true =>
      simp only [d92779, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h4 (q : Pattern) (ha : d92823 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92823, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92823, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92829 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92830 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92830, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92830, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92831 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92831, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92831, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92832 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92832, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92832, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92838 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92842 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92845 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92788 q = 1) (hb : d112059 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92788, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17606 q ha hb
    | true =>
      simp only [d92788, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h13 (q : Pattern) (ha : d92846 q = 1) (hb : d112060 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92846, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92846, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d92849 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92850 q = 1) (hb : d112061 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92850, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92850, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92851 q = 1) (hb : d112062 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92851, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d92851, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92852 q = 1) (hb : d112063 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92852, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d92852, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92853 q = 1) (hb : d112064 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92853, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92853, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17755 (p : Pattern) (ha : d92867 p = 1) (hb : d112552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92788 q = 1) (hb : d112059 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92788, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17606 q ha hb
    | true =>
      simp only [d92788, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h3 (q : Pattern) (ha : d92846 q = 1) (hb : d112060 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92846, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92846, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92849 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92850 q = 1) (hb : d112061 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92850, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92850, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92865 q = 1) (hb : d112062 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92865, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92865, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92866 q = 1) (hb : d112063 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92866, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92866, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92867 q = 1) (hb : d112552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92867, d112552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92867, d112552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17756 (p : Pattern) (ha : d92894 p = 1) (hb : d112144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92889 q = 1) (hb : d99000 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92889, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17628 q ha hb
    | true =>
      simp only [d92889, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92890 q = 1) (hb : d99001 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92890, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92890, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d52919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro169 q ha hb
    | true =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92891 q = 1) (hb : d112141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92891, d112141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92891, d112141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92892 q = 1) (hb : d112142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92892, d112142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92892, d112142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92893 q = 1) (hb : d112143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92893, d112143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92893, d112143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92894 q = 1) (hb : d112144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92894, d112144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92894, d112144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17757 (p : Pattern) (ha : d92906 p = 1) (hb : d112563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92886 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92895 q = 1) (hb : d112558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92895, d112558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17756 q ha hb
    | true =>
      simp only [d92895, d112558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro170 q hb ha
  have h3 (q : Pattern) (ha : d92896 q = 1) (hb : d112559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92896, d112559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92896, d112559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92903 q = 1) (hb : d112560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92903, d112560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92903, d112560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92904 q = 1) (hb : d112561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92904, d112561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92904, d112561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92905 q = 1) (hb : d112562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92905, d112562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92905, d112562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92906 q = 1) (hb : d112563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92906, d112563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92906, d112563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17758 (p : Pattern) (ha : d92912 p = 1) (hb : d112569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92796 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92854 q = 1) (hb : d112065 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92854, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17753 q ha hb
    | true =>
      simp only [d92854, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17754 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92861 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92862 q = 1) (hb : d112066 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92862, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92862, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92863 q = 1) (hb : d112550 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92863, d112550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92863, d112550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92864 q = 1) (hb : d112551 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92864, d112551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92864, d112551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92868 q = 1) (hb : d112553 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92868, d112553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92868, d112553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17755 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d92869 q = 1) (hb : d112554 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92869, d112554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92869, d112554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92870 q = 1) (hb : d112555 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92870, d112555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92870, d112555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92871 q = 1) (hb : d112556 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92871, d112556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92871, d112556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d92872 q = 1) (hb : d112557 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92872, d112557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92872, d112557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92907 q = 1) (hb : d112564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92907, d112564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92907, d112564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17757 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92908 q = 1) (hb : d112565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92908, d112565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92908, d112565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92909 q = 1) (hb : d112566 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92909, d112566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92909, d112566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92910 q = 1) (hb : d112567 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92910, d112567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92910, d112567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d92911 q = 1) (hb : d112568 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92911, d112568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92911, d112568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d92912 q = 1) (hb : d112569 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92912, d112569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92912, d112569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17759 (p : Pattern) (ha : d92918 p = 1) (hb : d112575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92913 q = 1) (hb : d112570 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92913, d112570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92913, d112570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17758 q ha hb
  have h2 (q : Pattern) (ha : d92914 q = 1) (hb : d112571 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92914, d112571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92914, d112571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92915 q = 1) (hb : d112572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92915, d112572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92915, d112572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92916 q = 1) (hb : d112573 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92916, d112573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92916, d112573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92917 q = 1) (hb : d112574 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92917, d112574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92917, d112574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92918 q = 1) (hb : d112575 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92918, d112575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92918, d112575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17760 (p : Pattern) (ha : d92984 p = 1) (hb : d112181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92953 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92959 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92973 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92930 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92930, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17634 q ha hb
    | true =>
      simp only [d92930, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h5 (q : Pattern) (ha : d92974 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92974, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92974, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92980 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92981 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92981, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92981, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92982 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92982, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92982, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92983 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92983, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92983, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92984 q = 1) (hb : d112181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92984, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92984, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17761 (p : Pattern) (ha : d93004 p = 1) (hb : d112190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92953 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92959 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92973 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92930 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92930, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17634 q ha hb
    | true =>
      simp only [d92930, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h4 (q : Pattern) (ha : d92974 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92974, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92974, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92980 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92981 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92981, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92981, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92982 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92982, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92982, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92983 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92983, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92983, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92989 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92993 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92996 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92939 q = 1) (hb : d112185 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92939, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17636 q ha hb
    | true =>
      simp only [d92939, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h13 (q : Pattern) (ha : d92997 q = 1) (hb : d112186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92997, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92997, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d93000 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93001 q = 1) (hb : d112187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93001, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93001, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d93002 q = 1) (hb : d112188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93002, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d93002, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93003 q = 1) (hb : d112189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93003, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d93003, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93004 q = 1) (hb : d112190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93004, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93004, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17762 (p : Pattern) (ha : d93018 p = 1) (hb : d112581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92996 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92939 q = 1) (hb : d112185 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92939, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17636 q ha hb
    | true =>
      simp only [d92939, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h3 (q : Pattern) (ha : d92997 q = 1) (hb : d112186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92997, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92997, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93000 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93001 q = 1) (hb : d112187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93001, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93001, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93016 q = 1) (hb : d112188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93016, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93016, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93017 q = 1) (hb : d112189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93017, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93017, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93018 q = 1) (hb : d112581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93018, d112581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93018, d112581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17763 (p : Pattern) (ha : d93045 p = 1) (hb : d112270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93040 q = 1) (hb : d99062 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93040, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17658 q ha hb
    | true =>
      simp only [d93040, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93041 q = 1) (hb : d99063 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93041, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93041, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro227 q ha hb
    | true =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93042 q = 1) (hb : d112267 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93042, d112267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93042, d112267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93043 q = 1) (hb : d112268 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93043, d112268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93043, d112268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93044 q = 1) (hb : d112269 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93044, d112269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93044, d112269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93045 q = 1) (hb : d112270 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93045, d112270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93045, d112270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17764 (p : Pattern) (ha : d93057 p = 1) (hb : d112592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93037 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d93046 q = 1) (hb : d112587 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93046, d112587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17763 q ha hb
    | true =>
      simp only [d93046, d112587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro228 q hb ha
  have h3 (q : Pattern) (ha : d93047 q = 1) (hb : d112588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93047, d112588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93047, d112588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93053 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93054 q = 1) (hb : d112589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93054, d112589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93054, d112589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93055 q = 1) (hb : d112590 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93055, d112590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93055, d112590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93056 q = 1) (hb : d112591 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93056, d112591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93056, d112591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93057 q = 1) (hb : d112592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93057, d112592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93057, d112592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17765 (p : Pattern) (ha : d93063 p = 1) (hb : d112598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92947 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93005 q = 1) (hb : d112191 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93005, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17760 q ha hb
    | true =>
      simp only [d93005, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17761 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93012 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93013 q = 1) (hb : d112192 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93013, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93013, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93014 q = 1) (hb : d112579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93014, d112579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93014, d112579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93015 q = 1) (hb : d112580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93015, d112580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93015, d112580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93019 q = 1) (hb : d112582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93019, d112582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93019, d112582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17762 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d93020 q = 1) (hb : d112583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93020, d112583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93020, d112583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d93021 q = 1) (hb : d112584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93021, d112584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93021, d112584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d93022 q = 1) (hb : d112585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93022, d112585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93022, d112585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d93023 q = 1) (hb : d112586 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93023, d112586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93023, d112586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d93058 q = 1) (hb : d112593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93058, d112593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93058, d112593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17764 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93059 q = 1) (hb : d112594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93059, d112594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93059, d112594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d93060 q = 1) (hb : d112595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93060, d112595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93060, d112595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d93061 q = 1) (hb : d112596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93061, d112596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d93061, d112596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d93062 q = 1) (hb : d112597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93062, d112597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93062, d112597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d93063 q = 1) (hb : d112598 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d93063, d112598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93063, d112598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17766 (p : Pattern) (ha : d93069 p = 1) (hb : d112604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93064 q = 1) (hb : d112599 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d93064, d112599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93064, d112599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17765 q ha hb
  have h2 (q : Pattern) (ha : d93065 q = 1) (hb : d112600 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d93065, d112600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93065, d112600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93066 q = 1) (hb : d112601 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d93066, d112601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93066, d112601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93067 q = 1) (hb : d112602 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d93067, d112602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93067, d112602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93068 q = 1) (hb : d112603 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d93068, d112603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93068, d112603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93069 q = 1) (hb : d112604 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d93069, d112604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93069, d112604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17767 (p : Pattern) (ha : d93136 p = 1) (hb : d112308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93111 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93125 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d93082 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93082, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17664 q ha hb
    | true =>
      simp only [d93082, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h5 (q : Pattern) (ha : d93126 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93126, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d93126, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d93132 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d93133 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93133, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93133, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d93134 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93134, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93134, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93135 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93135, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93135, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93136 q = 1) (hb : d112308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93136, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93136, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17768 (p : Pattern) (ha : d93156 p = 1) (hb : d112317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d93105 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93111 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93082 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93082, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17664 q ha hb
    | true =>
      simp only [d93082, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h4 (q : Pattern) (ha : d93126 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93126, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d93126, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d93132 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d93133 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93133, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93133, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d93134 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93134, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93134, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93135 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93135, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93135, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d93141 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d93145 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d93148 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d93091 q = 1) (hb : d112312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93091, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17666 q ha hb
    | true =>
      simp only [d93091, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h13 (q : Pattern) (ha : d93149 q = 1) (hb : d112313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93149, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d93149, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d93152 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93153 q = 1) (hb : d112314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93153, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93153, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d93154 q = 1) (hb : d112315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93154, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d93154, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93155 q = 1) (hb : d112316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93155, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d93155, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93156 q = 1) (hb : d112317 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93156, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93156, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17769 (p : Pattern) (ha : d93170 p = 1) (hb : d112611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93148 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d93091 q = 1) (hb : d112312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93091, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17666 q ha hb
    | true =>
      simp only [d93091, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h3 (q : Pattern) (ha : d93149 q = 1) (hb : d112313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93149, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93149, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93152 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93153 q = 1) (hb : d112314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93153, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93153, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93168 q = 1) (hb : d112315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93168, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93168, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93169 q = 1) (hb : d112316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93169, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93169, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93170 q = 1) (hb : d112611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93170, d112611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93170, d112611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17770 (p : Pattern) (ha : d93197 p = 1) (hb : d112397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93192 q = 1) (hb : d99125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93192, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17688 q ha hb
    | true =>
      simp only [d93192, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93193 q = 1) (hb : d99126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93193, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93193, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro286 q ha hb
    | true =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93194 q = 1) (hb : d112394 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93194, d112394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93194, d112394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93195 q = 1) (hb : d112395 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93195, d112395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93195, d112395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93196 q = 1) (hb : d112396 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93196, d112396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93196, d112396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93197 q = 1) (hb : d112397 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93197, d112397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93197, d112397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17771 (p : Pattern) (ha : d93209 p = 1) (hb : d112622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d93189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d93198 q = 1) (hb : d112617 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93198, d112617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17770 q ha hb
    | true =>
      simp only [d93198, d112617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro287 q hb ha
  have h3 (q : Pattern) (ha : d93199 q = 1) (hb : d112618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93199, d112618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93199, d112618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93205 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93206 q = 1) (hb : d112619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93206, d112619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93206, d112619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93207 q = 1) (hb : d112620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93207, d112620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93207, d112620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93208 q = 1) (hb : d112621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93208, d112621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93208, d112621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93209 q = 1) (hb : d112622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93209, d112622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93209, d112622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17772 (p : Pattern) (ha : d93215 p = 1) (hb : d112628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d93099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93157 q = 1) (hb : d112318 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93157, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17767 q ha hb
    | true =>
      simp only [d93157, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17768 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93165 q = 1) (hb : d112319 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93165, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93165, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93166 q = 1) (hb : d112609 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93166, d112609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93166, d112609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93167 q = 1) (hb : d112610 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93167, d112610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93167, d112610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93171 q = 1) (hb : d112612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93171, d112612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93171, d112612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17769 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d93172 q = 1) (hb : d112613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93172, d112613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93172, d112613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d93173 q = 1) (hb : d112614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93173, d112614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93173, d112614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d93174 q = 1) (hb : d112615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93174, d112615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93174, d112615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d93175 q = 1) (hb : d112616 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93175, d112616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93175, d112616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d93210 q = 1) (hb : d112623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93210, d112623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d93210, d112623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17771 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93211 q = 1) (hb : d112624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93211, d112624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93211, d112624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d93212 q = 1) (hb : d112625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93212, d112625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93212, d112625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d93213 q = 1) (hb : d112626 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93213, d112626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d93213, d112626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d93214 q = 1) (hb : d112627 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93214, d112627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93214, d112627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d93215 q = 1) (hb : d112628 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d93215, d112628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93215, d112628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17773 (p : Pattern) (ha : d93221 p = 1) (hb : d112634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93216 q = 1) (hb : d112629 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d93216, d112629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93216, d112629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17772 q ha hb
  have h2 (q : Pattern) (ha : d93217 q = 1) (hb : d112630 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d93217, d112630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93217, d112630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93218 q = 1) (hb : d112631 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d93218, d112631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93218, d112631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93219 q = 1) (hb : d112632 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d93219, d112632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93219, d112632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93220 q = 1) (hb : d112633 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d93220, d112633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93220, d112633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93221 q = 1) (hb : d112634 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d93221, d112634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93221, d112634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17774 (p : Pattern) (ha : d93227 p = 1) (hb : d112640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d92620 q = 1) (hb : d112521 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92620, d112521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17738 q ha hb
    | true =>
      simp only [d92620, d112521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17745 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92769 q = 1) (hb : d112548 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92769, d112548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92769, d112548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17752 q ha hb
  have h3 (q : Pattern) (ha : d92770 q = 1) (hb : d112549 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d92770, d112549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d92770, d112549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92919 q = 1) (hb : d112576 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92919, d112576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92919, d112576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17759 q ha hb
  have h5 (q : Pattern) (ha : d92920 q = 1) (hb : d112577 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d92920, d112577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92920, d112577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92921 q = 1) (hb : d112578 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d92921, d112578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92921, d112578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93070 q = 1) (hb : d112605 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d93070, d112605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93070, d112605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17766 q ha hb
  have h8 (q : Pattern) (ha : d93071 q = 1) (hb : d112606 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d93071, d112606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93071, d112606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93072 q = 1) (hb : d112607 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d93072, d112607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93072, d112607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93073 q = 1) (hb : d112608 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d93073, d112608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93073, d112608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93222 q = 1) (hb : d112635 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d93222, d112635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93222, d112635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17773 q ha hb
  have h12 (q : Pattern) (ha : d93223 q = 1) (hb : d112636 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d93223, d112636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93223, d112636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d93224 q = 1) (hb : d112637 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d93224, d112637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93224, d112637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d93225 q = 1) (hb : d112638 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d93225, d112638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93225, d112638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d93226 q = 1) (hb : d112639 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d93226, d112639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93226, d112639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93227 q = 1) (hb : d112640 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d93227, d112640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93227, d112640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro17775 (p : Pattern) (ha : d93233 p = 1) (hb : d112646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93228 q = 1) (hb : d112641 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d93228, d112641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17774 q ha hb
    | true =>
      simp only [d93228, d112641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93229 q = 1) (hb : d112642 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d93229, d112642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93229, d112642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93230 q = 1) (hb : d112643 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d93230, d112643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93230, d112643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93231 q = 1) (hb : d112644 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d93231, d112644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93231, d112644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93232 q = 1) (hb : d112645 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d93232, d112645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93232, d112645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93233 q = 1) (hb : d112646 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d93233, d112646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93233, d112646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17776 (p : Pattern) (ha : d93239 p = 1) (hb : d112652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93234 q = 1) (hb : d112647 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d93234, d112647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17775 q ha hb
    | true =>
      simp only [d93234, d112647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93235 q = 1) (hb : d112648 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d93235, d112648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93235, d112648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93236 q = 1) (hb : d112649 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d93236, d112649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93236, d112649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93237 q = 1) (hb : d112650 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d93237, d112650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93237, d112650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93238 q = 1) (hb : d112651 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d93238, d112651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93238, d112651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93239 q = 1) (hb : d112652 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d93239, d112652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93239, d112652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17777 (p : Pattern) (ha : d93245 p = 1) (hb : d112658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93240 q = 1) (hb : d112653 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d93240, d112653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17776 q ha hb
    | true =>
      simp only [d93240, d112653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93241 q = 1) (hb : d112654 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d93241, d112654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93241, d112654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93242 q = 1) (hb : d112655 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d93242, d112655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93242, d112655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93243 q = 1) (hb : d112656 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d93243, d112656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93243, d112656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93244 q = 1) (hb : d112657 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d93244, d112657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93244, d112657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93245 q = 1) (hb : d112658 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d93245, d112658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93245, d112658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17778 (p : Pattern) (ha : d93251 p = 1) (hb : d112664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93246 q = 1) (hb : d112659 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d93246, d112659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17777 q ha hb
    | true =>
      simp only [d93246, d112659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93247 q = 1) (hb : d112660 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d93247, d112660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93247, d112660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93248 q = 1) (hb : d112661 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d93248, d112661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93248, d112661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93249 q = 1) (hb : d112662 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d93249, d112662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93249, d112662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93250 q = 1) (hb : d112663 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d93250, d112663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93250, d112663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93251 q = 1) (hb : d112664 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d93251, d112664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93251, d112664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17779 (p : Pattern) (ha : d93257 p = 1) (hb : d112670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93252 q = 1) (hb : d112665 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d93252, d112665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17778 q ha hb
    | true =>
      simp only [d93252, d112665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93253 q = 1) (hb : d112666 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d93253, d112666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93253, d112666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93254 q = 1) (hb : d112667 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d93254, d112667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93254, d112667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93255 q = 1) (hb : d112668 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d93255, d112668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93255, d112668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93256 q = 1) (hb : d112669 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d93256, d112669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93256, d112669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93257 q = 1) (hb : d112670 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d93257, d112670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93257, d112670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17780 (p : Pattern) (ha : d93263 p = 1) (hb : d112676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93258 q = 1) (hb : d112671 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d93258, d112671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17779 q ha hb
    | true =>
      simp only [d93258, d112671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93259 q = 1) (hb : d112672 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d93259, d112672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93259, d112672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93260 q = 1) (hb : d112673 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d93260, d112673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93260, d112673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93261 q = 1) (hb : d112674 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d93261, d112674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93261, d112674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93262 q = 1) (hb : d112675 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d93262, d112675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93262, d112675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93263 q = 1) (hb : d112676 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d93263, d112676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93263, d112676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17781 (p : Pattern) (ha : d93269 p = 1) (hb : d112682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93264 q = 1) (hb : d112677 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d93264, d112677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17780 q ha hb
    | true =>
      simp only [d93264, d112677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93265 q = 1) (hb : d112678 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d93265, d112678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93265, d112678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93266 q = 1) (hb : d112679 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d93266, d112679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93266, d112679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93267 q = 1) (hb : d112680 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d93267, d112680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93267, d112680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93268 q = 1) (hb : d112681 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d93268, d112681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93268, d112681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93269 q = 1) (hb : d112682 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d93269, d112682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93269, d112682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17782 (p : Pattern) (ha : d94229 p = 1) (hb : d111718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8320 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94225 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94225, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8336 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94226 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94226, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94227 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94227, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94228 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94228, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94229 q = 1) (hb : d111718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94229, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94229, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17783 (p : Pattern) (ha : d94234 p = 1) (hb : d111725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8320 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94225 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94225, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8336 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94226 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94226, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94227 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94227, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94228 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94228, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8345 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8349 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8351 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94230 q = 1) (hb : d111721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94230, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94231 q = 1) (hb : d111722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94231, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94232 q = 1) (hb : d111723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94232, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94232, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94233 q = 1) (hb : d111724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94233, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94233, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94234 q = 1) (hb : d111725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94234, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94234, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17784 (p : Pattern) (ha : d94241 p = 1) (hb : d112472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94230 q = 1) (hb : d111721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94230, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94231 q = 1) (hb : d111722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94231, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94239 q = 1) (hb : d111723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94239, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94239, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94240 q = 1) (hb : d111724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94240, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94240, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94241 q = 1) (hb : d112472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94241, d112472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94241, d112472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17785 (p : Pattern) (ha : d94251 p = 1) (hb : d112482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8384 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111697 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94247 q = 1) (hb : d112478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94247, d112478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94247, d112478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8400 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94248 q = 1) (hb : d112479 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94248, d112479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94248, d112479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94249 q = 1) (hb : d112480 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94249, d112480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94249, d112480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94250 q = 1) (hb : d112481 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94250, d112481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94250, d112481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94251 q = 1) (hb : d112482 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94251, d112482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94251, d112482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17786 (p : Pattern) (ha : d94257 p = 1) (hb : d112488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94235 q = 1) (hb : d111726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94235, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17782 q ha hb
    | true =>
      simp only [d94235, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17783 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8364 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94236 q = 1) (hb : d111727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94236, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94236, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94237 q = 1) (hb : d112470 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94237, d112470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94237, d112470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94238 q = 1) (hb : d112471 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94238, d112471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94238, d112471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94242 q = 1) (hb : d112473 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94242, d112473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94242, d112473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17784 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94243 q = 1) (hb : d112474 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94243, d112474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94243, d112474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94244 q = 1) (hb : d112475 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94244, d112475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94244, d112475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94245 q = 1) (hb : d112476 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94245, d112476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94245, d112476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94246 q = 1) (hb : d112477 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94246, d112477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94246, d112477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94252 q = 1) (hb : d112483 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94252, d112483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94252, d112483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17785 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94253 q = 1) (hb : d112484 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94253, d112484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94253, d112484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94254 q = 1) (hb : d112485 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94254, d112485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94254, d112485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94255 q = 1) (hb : d112486 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94255, d112486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94255, d112486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94256 q = 1) (hb : d112487 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94256, d112487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94256, d112487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94257 q = 1) (hb : d112488 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94257, d112488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94257, d112488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17787 (p : Pattern) (ha : d94263 p = 1) (hb : d112494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d94220 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d94220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d94220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11648 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d94221 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d94221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d94221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d94222 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d94222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d94222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d94223 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d94223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d94223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d94224 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d94224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d94224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94258 q = 1) (hb : d112489 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94258, d112489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94258, d112489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17786 q ha hb
  have h8 (q : Pattern) (ha : d94259 q = 1) (hb : d112490 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94259, d112490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94259, d112490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94260 q = 1) (hb : d112491 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94260, d112491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94260, d112491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94261 q = 1) (hb : d112492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94261, d112492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94261, d112492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94262 q = 1) (hb : d112493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94262, d112493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94262, d112493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94263 q = 1) (hb : d112494 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94263, d112494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d94263, d112494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro17788 (p : Pattern) (ha : d94268 p = 1) (hb : d111811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8444 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8450 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8464 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94264 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94264, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8481 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94265 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94265, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94266 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94266, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94267 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94267, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94268 q = 1) (hb : d111811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94268, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94268, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17789 (p : Pattern) (ha : d94273 p = 1) (hb : d111819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8450 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8464 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94264 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94264, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8481 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94265 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94265, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94266 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94266, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94267 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94267, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8490 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8494 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8497 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d111814 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94269 q = 1) (hb : d111815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94269, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8503 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94270 q = 1) (hb : d111816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94270, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94271 q = 1) (hb : d111817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94271, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94271, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94272 q = 1) (hb : d111818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94272, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94272, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94273 q = 1) (hb : d111819 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94273, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94273, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17790 (p : Pattern) (ha : d94280 p = 1) (hb : d112497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8497 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111814 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94269 q = 1) (hb : d111815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94269, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8503 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94270 q = 1) (hb : d111816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94270, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94278 q = 1) (hb : d111817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94278, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94278, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94279 q = 1) (hb : d111818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94279, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94279, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94280 q = 1) (hb : d112497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94280, d112497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94280, d112497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17791 (p : Pattern) (ha : d94290 p = 1) (hb : d112508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8540 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112503 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94286 q = 1) (hb : d112504 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94286, d112504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94286, d112504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8557 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94287 q = 1) (hb : d112505 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94287, d112505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94287, d112505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94288 q = 1) (hb : d112506 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94288, d112506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94288, d112506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94289 q = 1) (hb : d112507 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94289, d112507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94289, d112507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94290 q = 1) (hb : d112508 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94290, d112508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94290, d112508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17792 (p : Pattern) (ha : d94296 p = 1) (hb : d112514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8438 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94274 q = 1) (hb : d111820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94274, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17788 q ha hb
    | true =>
      simp only [d94274, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17789 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8515 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94275 q = 1) (hb : d111821 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94275, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94275, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94276 q = 1) (hb : d112495 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94276, d112495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94276, d112495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94277 q = 1) (hb : d112496 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94277, d112496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94277, d112496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94281 q = 1) (hb : d112498 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94281, d112498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94281, d112498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17790 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94282 q = 1) (hb : d112499 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94282, d112499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94282, d112499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94283 q = 1) (hb : d112500 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94283, d112500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94283, d112500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94284 q = 1) (hb : d112501 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94284, d112501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94284, d112501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94285 q = 1) (hb : d112502 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94285, d112502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94285, d112502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94291 q = 1) (hb : d112509 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94291, d112509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94291, d112509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17791 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94292 q = 1) (hb : d112510 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94292, d112510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94292, d112510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94293 q = 1) (hb : d112511 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94293, d112511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94293, d112511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94294 q = 1) (hb : d112512 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94294, d112512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94294, d112512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94295 q = 1) (hb : d112513 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94295, d112513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94295, d112513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94296 q = 1) (hb : d112514 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94296, d112514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94296, d112514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17793 (p : Pattern) (ha : d94302 p = 1) (hb : d112520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94297 q = 1) (hb : d112515 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94297, d112515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94297, d112515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17792 q ha hb
  have h2 (q : Pattern) (ha : d94298 q = 1) (hb : d112516 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94298, d112516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94298, d112516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94299 q = 1) (hb : d112517 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94299, d112517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94299, d112517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94300 q = 1) (hb : d112518 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94300, d112518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94300, d112518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94301 q = 1) (hb : d112519 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94301, d112519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94301, d112519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94302 q = 1) (hb : d112520 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94302, d112520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94302, d112520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17794 (p : Pattern) (ha : d94308 p = 1) (hb : d111930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8606 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8612 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8626 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94304 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94304, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8643 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94305 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94305, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94306 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94306, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94307 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94307, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94308 q = 1) (hb : d111930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94308, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94308, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17795 (p : Pattern) (ha : d94313 p = 1) (hb : d111939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8606 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8612 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8626 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94304 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94304, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8643 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94305 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94305, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94306 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94306, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94307 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94307, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8652 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8656 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8659 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d111934 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94309 q = 1) (hb : d111935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94309, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8665 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94310 q = 1) (hb : d111936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94310, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94311 q = 1) (hb : d111937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94311, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94311, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94312 q = 1) (hb : d111938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94312, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94312, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94313 q = 1) (hb : d111939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94313, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94313, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17796 (p : Pattern) (ha : d94320 p = 1) (hb : d112524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94309 q = 1) (hb : d111935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94309, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8665 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94310 q = 1) (hb : d111936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94310, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94318 q = 1) (hb : d111937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94318, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94318, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94319 q = 1) (hb : d111938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94319, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94319, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94320 q = 1) (hb : d112524 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94320, d112524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94320, d112524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17797 (p : Pattern) (ha : d94330 p = 1) (hb : d112535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8702 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112530 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94326 q = 1) (hb : d112531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94326, d112531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94326, d112531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8723 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94327 q = 1) (hb : d112532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94327, d112532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94327, d112532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94328 q = 1) (hb : d112533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94328, d112533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94328, d112533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94329 q = 1) (hb : d112534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94329, d112534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94329, d112534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94330 q = 1) (hb : d112535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94330, d112535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94330, d112535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17798 (p : Pattern) (ha : d94336 p = 1) (hb : d112541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8600 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94314 q = 1) (hb : d111940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94314, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17794 q ha hb
    | true =>
      simp only [d94314, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17795 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8677 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94315 q = 1) (hb : d111941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94315, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94315, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94316 q = 1) (hb : d112522 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94316, d112522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94316, d112522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94317 q = 1) (hb : d112523 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94317, d112523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94317, d112523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94321 q = 1) (hb : d112525 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94321, d112525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94321, d112525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17796 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94322 q = 1) (hb : d112526 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94322, d112526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94322, d112526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94323 q = 1) (hb : d112527 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94323, d112527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94323, d112527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94324 q = 1) (hb : d112528 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94324, d112528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94324, d112528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94325 q = 1) (hb : d112529 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94325, d112529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94325, d112529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94331 q = 1) (hb : d112536 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94331, d112536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94331, d112536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17797 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94332 q = 1) (hb : d112537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94332, d112537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94332, d112537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94333 q = 1) (hb : d112538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94333, d112538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94333, d112538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94334 q = 1) (hb : d112539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94334, d112539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94334, d112539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94335 q = 1) (hb : d112540 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94335, d112540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94335, d112540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94336 q = 1) (hb : d112541 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94336, d112541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94336, d112541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17799 (p : Pattern) (ha : d94342 p = 1) (hb : d112547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94337 q = 1) (hb : d112542 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94337, d112542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94337, d112542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17798 q ha hb
  have h2 (q : Pattern) (ha : d94338 q = 1) (hb : d112543 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94338, d112543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94338, d112543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94339 q = 1) (hb : d112544 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94339, d112544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94339, d112544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94340 q = 1) (hb : d112545 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94340, d112545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94340, d112545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94341 q = 1) (hb : d112546 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94341, d112546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94341, d112546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94342 q = 1) (hb : d112547 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94342, d112547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94342, d112547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17800 (p : Pattern) (ha : d94349 p = 1) (hb : d112055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8793 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94345 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94345, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8810 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94346 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94346, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94347 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94347, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94348 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94348, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94349 q = 1) (hb : d112055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94349, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94349, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17801 (p : Pattern) (ha : d94354 p = 1) (hb : d112064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8793 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94345 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94345, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8810 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94346 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94346, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94347 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94347, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94348 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94348, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8819 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8823 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8826 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112059 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94350 q = 1) (hb : d112060 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94350, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8832 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94351 q = 1) (hb : d112061 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94351, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94352 q = 1) (hb : d112062 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94352, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94352, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94353 q = 1) (hb : d112063 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94353, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94353, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94354 q = 1) (hb : d112064 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94354, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94354, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17802 (p : Pattern) (ha : d94361 p = 1) (hb : d112552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112059 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94350 q = 1) (hb : d112060 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94350, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94351 q = 1) (hb : d112061 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94351, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94359 q = 1) (hb : d112062 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94359, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94359, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94360 q = 1) (hb : d112063 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94360, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94360, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94361 q = 1) (hb : d112552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94361, d112552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94361, d112552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17803 (p : Pattern) (ha : d94371 p = 1) (hb : d112563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8869 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112558 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94367 q = 1) (hb : d112559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94367, d112559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94367, d112559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8890 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94368 q = 1) (hb : d112560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94368, d112560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94368, d112560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94369 q = 1) (hb : d112561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94369, d112561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94369, d112561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94370 q = 1) (hb : d112562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94370, d112562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94370, d112562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94371 q = 1) (hb : d112563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94371, d112563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94371, d112563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17804 (p : Pattern) (ha : d94377 p = 1) (hb : d112569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8767 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94355 q = 1) (hb : d112065 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94355, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17800 q ha hb
    | true =>
      simp only [d94355, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17801 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8844 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94356 q = 1) (hb : d112066 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94356, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94356, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94357 q = 1) (hb : d112550 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94357, d112550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94357, d112550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94358 q = 1) (hb : d112551 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94358, d112551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94358, d112551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94362 q = 1) (hb : d112553 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94362, d112553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94362, d112553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17802 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94363 q = 1) (hb : d112554 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94363, d112554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94363, d112554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94364 q = 1) (hb : d112555 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94364, d112555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94364, d112555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94365 q = 1) (hb : d112556 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94365, d112556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94365, d112556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94366 q = 1) (hb : d112557 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94366, d112557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94366, d112557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94372 q = 1) (hb : d112564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94372, d112564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94372, d112564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17803 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94373 q = 1) (hb : d112565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94373, d112565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94373, d112565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94374 q = 1) (hb : d112566 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94374, d112566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94374, d112566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94375 q = 1) (hb : d112567 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94375, d112567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94375, d112567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94376 q = 1) (hb : d112568 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94376, d112568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94376, d112568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94377 q = 1) (hb : d112569 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94377, d112569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94377, d112569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17805 (p : Pattern) (ha : d94383 p = 1) (hb : d112575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94378 q = 1) (hb : d112570 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94378, d112570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94378, d112570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17804 q ha hb
  have h2 (q : Pattern) (ha : d94379 q = 1) (hb : d112571 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94379, d112571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94379, d112571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94380 q = 1) (hb : d112572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94380, d112572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94380, d112572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94381 q = 1) (hb : d112573 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94381, d112573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94381, d112573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94382 q = 1) (hb : d112574 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94382, d112574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94382, d112574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94383 q = 1) (hb : d112575 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94383, d112575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94383, d112575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17806 (p : Pattern) (ha : d94391 p = 1) (hb : d112181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8941 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8947 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8961 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94387 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94387, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8978 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94388 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94388, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94389 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94389, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94390 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94390, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94391 q = 1) (hb : d112181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94391, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94391, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17807 (p : Pattern) (ha : d94396 p = 1) (hb : d112190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8947 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8961 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94387 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94387, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8978 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94388 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94388, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94389 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94389, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94390 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94390, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8987 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8991 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8994 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112185 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94392 q = 1) (hb : d112186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94392, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9000 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94393 q = 1) (hb : d112187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94393, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94394 q = 1) (hb : d112188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94394, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94394, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94395 q = 1) (hb : d112189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94395, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94395, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94396 q = 1) (hb : d112190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94396, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94396, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17808 (p : Pattern) (ha : d94403 p = 1) (hb : d112581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112185 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94392 q = 1) (hb : d112186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94392, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9000 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94393 q = 1) (hb : d112187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94393, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94401 q = 1) (hb : d112188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94401, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94401, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94402 q = 1) (hb : d112189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94402, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94402, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94403 q = 1) (hb : d112581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94403, d112581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94403, d112581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17809 (p : Pattern) (ha : d94413 p = 1) (hb : d112592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9037 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112587 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94409 q = 1) (hb : d112588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94409, d112588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94409, d112588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9058 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94410 q = 1) (hb : d112589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94410, d112589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94410, d112589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94411 q = 1) (hb : d112590 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94411, d112590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94411, d112590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94412 q = 1) (hb : d112591 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94412, d112591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94412, d112591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94413 q = 1) (hb : d112592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94413, d112592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94413, d112592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17810 (p : Pattern) (ha : d94419 p = 1) (hb : d112598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94397 q = 1) (hb : d112191 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94397, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17806 q ha hb
    | true =>
      simp only [d94397, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17807 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9012 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94398 q = 1) (hb : d112192 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94398, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94398, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94399 q = 1) (hb : d112579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94399, d112579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94399, d112579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94400 q = 1) (hb : d112580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94400, d112580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94400, d112580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94404 q = 1) (hb : d112582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94404, d112582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94404, d112582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17808 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94405 q = 1) (hb : d112583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94405, d112583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94405, d112583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94406 q = 1) (hb : d112584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94406, d112584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94406, d112584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94407 q = 1) (hb : d112585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94407, d112585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94407, d112585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94408 q = 1) (hb : d112586 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94408, d112586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94408, d112586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94414 q = 1) (hb : d112593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94414, d112593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94414, d112593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17809 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94415 q = 1) (hb : d112594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94415, d112594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94415, d112594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94416 q = 1) (hb : d112595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94416, d112595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94416, d112595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94417 q = 1) (hb : d112596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94417, d112596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94417, d112596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94418 q = 1) (hb : d112597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94418, d112597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94418, d112597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94419 q = 1) (hb : d112598 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94419, d112598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94419, d112598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17811 (p : Pattern) (ha : d94425 p = 1) (hb : d112604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94420 q = 1) (hb : d112599 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94420, d112599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94420, d112599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17810 q ha hb
  have h2 (q : Pattern) (ha : d94421 q = 1) (hb : d112600 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94421, d112600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94421, d112600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94422 q = 1) (hb : d112601 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94422, d112601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94422, d112601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94423 q = 1) (hb : d112602 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94423, d112602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94423, d112602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94424 q = 1) (hb : d112603 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94424, d112603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94424, d112603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94425 q = 1) (hb : d112604 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94425, d112604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94425, d112604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17812 (p : Pattern) (ha : d94434 p = 1) (hb : d112308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9116 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d9130 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94430 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94430, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94431 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94431, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94432 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94432, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94433 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94433, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94434 q = 1) (hb : d112308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94434, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94434, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17813 (p : Pattern) (ha : d94439 p = 1) (hb : d112317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9110 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9116 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94430 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94430, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9147 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94431 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94431, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94432 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94432, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94433 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94433, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9156 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d9160 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d9163 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112312 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94435 q = 1) (hb : d112313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94435, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9169 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94436 q = 1) (hb : d112314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94436, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94437 q = 1) (hb : d112315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94437, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94437, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94438 q = 1) (hb : d112316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94438, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94438, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94439 q = 1) (hb : d112317 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94439, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94439, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17814 (p : Pattern) (ha : d94446 p = 1) (hb : d112611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9163 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94435 q = 1) (hb : d112313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94435, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9169 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94436 q = 1) (hb : d112314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94436, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94444 q = 1) (hb : d112315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94444, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94444, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94445 q = 1) (hb : d112316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94445, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94445, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94446 q = 1) (hb : d112611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94446, d112611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94446, d112611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17815 (p : Pattern) (ha : d94456 p = 1) (hb : d112622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9206 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112617 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94452 q = 1) (hb : d112618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94452, d112618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94452, d112618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9227 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94453 q = 1) (hb : d112619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94453, d112619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94453, d112619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94454 q = 1) (hb : d112620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94454, d112620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94454, d112620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94455 q = 1) (hb : d112621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94455, d112621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94455, d112621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94456 q = 1) (hb : d112622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94456, d112622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94456, d112622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17816 (p : Pattern) (ha : d94462 p = 1) (hb : d112628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9104 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94440 q = 1) (hb : d112318 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94440, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17812 q ha hb
    | true =>
      simp only [d94440, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17813 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9181 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94441 q = 1) (hb : d112319 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94441, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94441, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94442 q = 1) (hb : d112609 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94442, d112609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94442, d112609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94443 q = 1) (hb : d112610 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94443, d112610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94443, d112610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94447 q = 1) (hb : d112612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94447, d112612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94447, d112612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17814 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94448 q = 1) (hb : d112613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94448, d112613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94448, d112613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94449 q = 1) (hb : d112614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94449, d112614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94449, d112614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94450 q = 1) (hb : d112615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94450, d112615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94450, d112615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94451 q = 1) (hb : d112616 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94451, d112616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94451, d112616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94457 q = 1) (hb : d112623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94457, d112623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94457, d112623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17815 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94458 q = 1) (hb : d112624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94458, d112624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94458, d112624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94459 q = 1) (hb : d112625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94459, d112625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94459, d112625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94460 q = 1) (hb : d112626 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94460, d112626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94460, d112626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94461 q = 1) (hb : d112627 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94461, d112627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94461, d112627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94462 q = 1) (hb : d112628 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94462, d112628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94462, d112628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17817 (p : Pattern) (ha : d94468 p = 1) (hb : d112634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94463 q = 1) (hb : d112629 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94463, d112629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94463, d112629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17816 q ha hb
  have h2 (q : Pattern) (ha : d94464 q = 1) (hb : d112630 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94464, d112630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94464, d112630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94465 q = 1) (hb : d112631 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94465, d112631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94465, d112631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94466 q = 1) (hb : d112632 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94466, d112632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94466, d112632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94467 q = 1) (hb : d112633 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94467, d112633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94467, d112633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94468 q = 1) (hb : d112634 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94468, d112634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94468, d112634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17818 (p : Pattern) (ha : d94474 p = 1) (hb : d112640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d94303 q = 1) (hb : d112521 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94303, d112521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17787 q ha hb
    | true =>
      simp only [d94303, d112521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17793 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94343 q = 1) (hb : d112548 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94343, d112548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94343, d112548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17799 q ha hb
  have h3 (q : Pattern) (ha : d94344 q = 1) (hb : d112549 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94344, d112549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94344, d112549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94384 q = 1) (hb : d112576 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94384, d112576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94384, d112576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17805 q ha hb
  have h5 (q : Pattern) (ha : d94385 q = 1) (hb : d112577 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94385, d112577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94385, d112577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94386 q = 1) (hb : d112578 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94386, d112578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94386, d112578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94426 q = 1) (hb : d112605 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94426, d112605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94426, d112605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17811 q ha hb
  have h8 (q : Pattern) (ha : d94427 q = 1) (hb : d112606 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94427, d112606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94427, d112606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94428 q = 1) (hb : d112607 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94428, d112607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94428, d112607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94429 q = 1) (hb : d112608 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94429, d112608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94429, d112608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94469 q = 1) (hb : d112635 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94469, d112635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94469, d112635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17817 q ha hb
  have h12 (q : Pattern) (ha : d94470 q = 1) (hb : d112636 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94470, d112636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94470, d112636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94471 q = 1) (hb : d112637 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94471, d112637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94471, d112637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94472 q = 1) (hb : d112638 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94472, d112638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94472, d112638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94473 q = 1) (hb : d112639 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94473, d112639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94473, d112639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94474 q = 1) (hb : d112640 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94474, d112640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94474, d112640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro17819 (p : Pattern) (ha : d94480 p = 1) (hb : d112646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94475 q = 1) (hb : d112641 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94475, d112641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17818 q ha hb
    | true =>
      simp only [d94475, d112641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94476 q = 1) (hb : d112642 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94476, d112642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94476, d112642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94477 q = 1) (hb : d112643 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94477, d112643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94477, d112643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94478 q = 1) (hb : d112644 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94478, d112644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94478, d112644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94479 q = 1) (hb : d112645 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94479, d112645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94479, d112645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94480 q = 1) (hb : d112646 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94480, d112646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94480, d112646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17820 (p : Pattern) (ha : d94486 p = 1) (hb : d112652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94481 q = 1) (hb : d112647 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94481, d112647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17819 q ha hb
    | true =>
      simp only [d94481, d112647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94482 q = 1) (hb : d112648 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94482, d112648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94482, d112648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94483 q = 1) (hb : d112649 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94483, d112649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94483, d112649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94484 q = 1) (hb : d112650 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94484, d112650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94484, d112650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94485 q = 1) (hb : d112651 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94485, d112651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94485, d112651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94486 q = 1) (hb : d112652 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94486, d112652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94486, d112652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17821 (p : Pattern) (ha : d94492 p = 1) (hb : d112658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94487 q = 1) (hb : d112653 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94487, d112653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17820 q ha hb
    | true =>
      simp only [d94487, d112653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94488 q = 1) (hb : d112654 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94488, d112654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94488, d112654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94489 q = 1) (hb : d112655 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94489, d112655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94489, d112655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94490 q = 1) (hb : d112656 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94490, d112656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94490, d112656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94491 q = 1) (hb : d112657 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94491, d112657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94491, d112657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94492 q = 1) (hb : d112658 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94492, d112658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94492, d112658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17822 (p : Pattern) (ha : d94498 p = 1) (hb : d112664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94493 q = 1) (hb : d112659 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94493, d112659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17821 q ha hb
    | true =>
      simp only [d94493, d112659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94494 q = 1) (hb : d112660 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94494, d112660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94494, d112660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94495 q = 1) (hb : d112661 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94495, d112661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94495, d112661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94496 q = 1) (hb : d112662 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94496, d112662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94496, d112662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94497 q = 1) (hb : d112663 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94497, d112663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94497, d112663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94498 q = 1) (hb : d112664 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94498, d112664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94498, d112664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17823 (p : Pattern) (ha : d94504 p = 1) (hb : d112670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94499 q = 1) (hb : d112665 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94499, d112665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17822 q ha hb
    | true =>
      simp only [d94499, d112665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94500 q = 1) (hb : d112666 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94500, d112666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94500, d112666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94501 q = 1) (hb : d112667 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94501, d112667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94501, d112667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94502 q = 1) (hb : d112668 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94502, d112668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94502, d112668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94503 q = 1) (hb : d112669 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94503, d112669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94503, d112669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94504 q = 1) (hb : d112670 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94504, d112670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94504, d112670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17824 (p : Pattern) (ha : d94510 p = 1) (hb : d112676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94505 q = 1) (hb : d112671 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94505, d112671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17823 q ha hb
    | true =>
      simp only [d94505, d112671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94506 q = 1) (hb : d112672 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94506, d112672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94506, d112672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94507 q = 1) (hb : d112673 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94507, d112673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94507, d112673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94508 q = 1) (hb : d112674 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94508, d112674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94508, d112674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94509 q = 1) (hb : d112675 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94509, d112675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94509, d112675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94510 q = 1) (hb : d112676 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94510, d112676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94510, d112676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17825 (p : Pattern) (ha : d94516 p = 1) (hb : d112682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94511 q = 1) (hb : d112677 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94511, d112677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17824 q ha hb
    | true =>
      simp only [d94511, d112677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94512 q = 1) (hb : d112678 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94512, d112678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94512, d112678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94513 q = 1) (hb : d112679 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94513, d112679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94513, d112679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94514 q = 1) (hb : d112680 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94514, d112680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94514, d112680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94515 q = 1) (hb : d112681 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94515, d112681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94515, d112681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94516 q = 1) (hb : d112682 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94516, d112682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94516, d112682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17826 (p : Pattern) (ha : d85719 p = 1) (hb : d104542 p = 1) : d85719 p = 1 := by
  have h0 (q : Pattern) (ha : d85719 q = 1) (hb : d104542 q = 1) : d85719 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro17827 (p : Pattern) (ha : d7247 p = 1) (hb : d52007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d7244 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7245 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7245, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7246 q = 1) (hb : d52006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7246, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7247 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7247, d52007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7247, d52007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17828 (p : Pattern) (ha : d52013 p = 1) (hb : d85394 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d7248 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17827 q ha hb
    | true =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52009 q = 1) (hb : d85390 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52009, d85390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52009, d85390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d52010 q = 1) (hb : d85391 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d85391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52010, d85391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d52011 q = 1) (hb : d85392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d85392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d52011, d85392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52012 q = 1) (hb : d85393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d85393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52012, d85393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52013 q = 1) (hb : d85394 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52013, d85394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52013, d85394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17829 (p : Pattern) (ha : d7254 p = 1) (hb : d52023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d7244 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7245 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7245, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7246 q = 1) (hb : d52006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7246, d52006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7254 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7254, d52023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7254, d52023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17830 (p : Pattern) (ha : d52029 p = 1) (hb : d85399 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d7248 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17827 q ha hb
    | true =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52009 q = 1) (hb : d85390 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52009, d85390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52009, d85390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d52010 q = 1) (hb : d85391 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52010, d85391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52010, d85391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d52011 q = 1) (hb : d85392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52011, d85392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d52011, d85392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52012 q = 1) (hb : d85393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52012, d85393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52012, d85393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d7255 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17829 q ha hb
    | true =>
      simp only [d7255, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52025 q = 1) (hb : d85395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52025, d85395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d52025, d85395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d52026 q = 1) (hb : d85396 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d85396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d52026, d85396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d52027 q = 1) (hb : d85397 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52027, d85397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d52027, d85397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d52028 q = 1) (hb : d85398 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52028, d85398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d52028, d85398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d52029 q = 1) (hb : d85399 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52029, d85399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52029, d85399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17831 (p : Pattern) (ha : d52038 p = 1) (hb : d85406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7255 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17829 q ha hb
    | true =>
      simp only [d7255, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52025 q = 1) (hb : d85395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52025, d85395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52025, d85395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d52026 q = 1) (hb : d85396 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52026, d85396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52026, d85396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52036 q = 1) (hb : d85404 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52036, d85404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52036, d85404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52037 q = 1) (hb : d85405 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52037, d85405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52037, d85405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52038 q = 1) (hb : d85406 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52038, d85406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52038, d85406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17832 (p : Pattern) (ha : d7280 p = 1) (hb : d52061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7275 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11703 q ha hb
    | true =>
      simp only [d7275, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7276 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d7277 q = 1) (hb : d52058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7277, d52058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7277, d52058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7278 q = 1) (hb : d52059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7278, d52059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7278, d52059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7279 q = 1) (hb : d52060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7279, d52060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7279, d52060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7280 q = 1) (hb : d52061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7280, d52061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7280, d52061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17833 (p : Pattern) (ha : d52067 p = 1) (hb : d85416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7281 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17832 q ha hb
    | true =>
      simp only [d7281, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52063 q = 1) (hb : d85412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52063, d85412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52063, d85412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d52064 q = 1) (hb : d85413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52064, d85413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52064, d85413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52065 q = 1) (hb : d85414 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52065, d85414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52065, d85414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52066 q = 1) (hb : d85415 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52066, d85415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52066, d85415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52067 q = 1) (hb : d85416 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52067, d85416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52067, d85416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17834 (p : Pattern) (ha : d52073 p = 1) (hb : d85422 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d52030 q = 1) (hb : d85400 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d85400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17828 q ha hb
    | true =>
      simp only [d52030, d85400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17830 q ha hb
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
  have h8 (q : Pattern) (ha : d52033 q = 1) (hb : d85401 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d85401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52033, d85401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52034 q = 1) (hb : d85402 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d85402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52034, d85402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52035 q = 1) (hb : d85403 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d85403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52035, d85403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52039 q = 1) (hb : d85407 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52039, d85407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52039, d85407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17831 q ha hb
  have h12 (q : Pattern) (ha : d52040 q = 1) (hb : d85408 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52040, d85408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52040, d85408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d52041 q = 1) (hb : d85409 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52041, d85409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52041, d85409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d52042 q = 1) (hb : d85410 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52042, d85410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52042, d85410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d52043 q = 1) (hb : d85411 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d85411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52043, d85411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52068 q = 1) (hb : d85417 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52068, d85417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52068, d85417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17833 q ha hb
  have h17 (q : Pattern) (ha : d52069 q = 1) (hb : d85418 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52069, d85418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52069, d85418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d52070 q = 1) (hb : d85419 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52070, d85419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52070, d85419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d52071 q = 1) (hb : d85420 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52071, d85420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d52071, d85420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d52072 q = 1) (hb : d85421 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52072, d85421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d52072, d85421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d52073 q = 1) (hb : d85422 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52073, d85422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52073, d85422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro17835 (p : Pattern) (ha : d7302 p = 1) (hb : d52083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7248 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17827 q ha hb
    | true =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d7298 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7299 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7299, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7300 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7301 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7302 q = 1) (hb : d52083 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7302, d52083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7302, d52083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17836 (p : Pattern) (ha : d7309 p = 1) (hb : d52090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7248 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17827 q ha hb
    | true =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d7298 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7299 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7299, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7300 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7301 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7255 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17829 q ha hb
    | true =>
      simp only [d7255, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h7 (q : Pattern) (ha : d7305 q = 1) (hb : d52086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d52086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7305, d52086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7306 q = 1) (hb : d52087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d52087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7306, d52087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7307 q = 1) (hb : d52088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d52088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d52088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7308 q = 1) (hb : d52089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d52089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d52089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7309 q = 1) (hb : d52090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7309, d52090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7309, d52090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17837 (p : Pattern) (ha : d7376 p = 1) (hb : d52163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7248 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17827 q ha hb
    | true =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d7298 q = 1) (hb : d52079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d52079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7299 q = 1) (hb : d52080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7299, d52080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7300 q = 1) (hb : d52081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d52081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7301 q = 1) (hb : d52082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d52082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d7376 q = 1) (hb : d52163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7376, d52163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7376, d52163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17838 (p : Pattern) (ha : d7314 p = 1) (hb : d52095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d7244 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7245 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7245, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7313 q = 1) (hb : d52094 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7314 q = 1) (hb : d52095 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7314, d52095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7314, d52095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17839 (p : Pattern) (ha : d7321 p = 1) (hb : d52102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d7244 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7319 q = 1) (hb : d52100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7320 q = 1) (hb : d52101 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7320, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7321 q = 1) (hb : d52102 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7321, d52102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7321, d52102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17840 (p : Pattern) (ha : d7332 p = 1) (hb : d52135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11711 q ha hb
    | true =>
      simp only [d7327, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7329 q = 1) (hb : d52132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7329, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7330 q = 1) (hb : d52133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7330, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7331 q = 1) (hb : d52134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7331, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7332 q = 1) (hb : d52135 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7332, d52135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7332, d52135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17841 (p : Pattern) (ha : d74080 p = 1) (hb : d85432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7315 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17838 q ha hb
    | true =>
      simp only [d7315, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d7316 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7317 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7317, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7318 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7322 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17839 q ha hb
    | true =>
      simp only [d7322, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d7323 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7324 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7324, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7333 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17840 q ha hb
    | true =>
      simp only [d7333, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17827 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52137 q = 1) (hb : d85428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52137, d85428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52137, d85428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7348 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11710 q ha hb
    | true =>
      simp only [d7348, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7349 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7349, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74077 q = 1) (hb : d85429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74077, d85429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74077, d85429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74078 q = 1) (hb : d85430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74078, d85430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74078, d85430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74079 q = 1) (hb : d85431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74079, d85431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74079, d85431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74080 q = 1) (hb : d85432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74080, d85432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74080, d85432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17842 (p : Pattern) (ha : d7354 p = 1) (hb : d52144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d7244 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7245 q = 1) (hb : d52005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7245, d52005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7313 q = 1) (hb : d52094 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d52094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7354 q = 1) (hb : d52144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7354, d52144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7354, d52144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17843 (p : Pattern) (ha : d7359 p = 1) (hb : d52149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d7244 q = 1) (hb : d52004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d52004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7319 q = 1) (hb : d52100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d52100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7320 q = 1) (hb : d52101 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7320, d52101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7359 q = 1) (hb : d52149 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7359, d52149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7359, d52149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17844 (p : Pattern) (ha : d7363 p = 1) (hb : d52153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11711 q ha hb
    | true =>
      simp only [d7327, d52130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7329 q = 1) (hb : d52132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7329, d52132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7330 q = 1) (hb : d52133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7330, d52133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7331 q = 1) (hb : d52134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7331, d52134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7363 q = 1) (hb : d52153 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7363, d52153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7363, d52153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17845 (p : Pattern) (ha : d74087 p = 1) (hb : d85437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7315 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17838 q ha hb
    | true =>
      simp only [d7315, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d7316 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7317 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7317, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7318 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7322 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17839 q ha hb
    | true =>
      simp only [d7322, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d7323 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7324 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7324, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7333 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17840 q ha hb
    | true =>
      simp only [d7333, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17827 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52137 q = 1) (hb : d85428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52137, d85428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52137, d85428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7348 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11710 q ha hb
    | true =>
      simp only [d7348, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7349 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7349, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74077 q = 1) (hb : d85429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74077, d85429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74077, d85429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74078 q = 1) (hb : d85430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74078, d85430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74078, d85430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74079 q = 1) (hb : d85431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74079, d85431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74079, d85431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7355 q = 1) (hb : d52145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7355, d52145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17842 q ha hb
    | true =>
      simp only [d7355, d52145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
  have h17 (q : Pattern) (ha : d7356 q = 1) (hb : d52146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7356, d52146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7356, d52146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7357 q = 1) (hb : d52147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7357, d52147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d7357, d52147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d7358 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7358, d52148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7358, d52148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7360 q = 1) (hb : d52150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7360, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17843 q ha hb
    | true =>
      simp only [d7360, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
  have h21 (q : Pattern) (ha : d7361 q = 1) (hb : d52151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7361, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7361, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7362 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7362, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7362, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d7364 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17844 q ha hb
    | true =>
      simp only [d7364, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17829 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52155 q = 1) (hb : d85433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52155, d85433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d52155, d85433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7369 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11716 q ha hb
    | true =>
      simp only [d7369, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d7370 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7370, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74084 q = 1) (hb : d85434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74084, d85434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74084, d85434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74085 q = 1) (hb : d85435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74085, d85435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d74085, d85435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74086 q = 1) (hb : d85436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74086, d85436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d74086, d85436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74087 q = 1) (hb : d85437 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74087, d85437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74087, d85437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17846 (p : Pattern) (ha : d74094 p = 1) (hb : d85444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7364 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17844 q ha hb
    | true =>
      simp only [d7364, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17829 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52155 q = 1) (hb : d85433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52155, d85433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52155, d85433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7369 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11716 q ha hb
    | true =>
      simp only [d7369, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7370 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7370, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74084 q = 1) (hb : d85434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74084, d85434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74084, d85434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74092 q = 1) (hb : d85442 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74092, d85442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74092, d85442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74093 q = 1) (hb : d85443 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74093, d85443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74093, d85443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74094 q = 1) (hb : d85444 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74094, d85444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74094, d85444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17847 (p : Pattern) (ha : d7396 p = 1) (hb : d52195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d52190 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d52190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11723 q ha hb
    | true =>
      simp only [d7391, d52190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d52191 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d52191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d52191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7275 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11703 q ha hb
    | true =>
      simp only [d7275, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7276 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7393 q = 1) (hb : d52192 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7393, d52192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7393, d52192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7394 q = 1) (hb : d52193 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7394, d52193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7394, d52193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7395 q = 1) (hb : d52194 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7395, d52194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7395, d52194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7396 q = 1) (hb : d52195 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7396, d52195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7396, d52195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17848 (p : Pattern) (ha : d74109 p = 1) (hb : d85454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7397 q = 1) (hb : d52196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7397, d52196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17847 q ha hb
    | true =>
      simp only [d7397, d52196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17832 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52197 q = 1) (hb : d85450 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52197, d85450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52197, d85450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7412 q = 1) (hb : d74104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7412, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11722 q ha hb
    | true =>
      simp only [d7412, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7413 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7413, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7413, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74106 q = 1) (hb : d85451 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74106, d85451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74106, d85451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74107 q = 1) (hb : d85452 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74107, d85452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74107, d85452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74108 q = 1) (hb : d85453 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74108, d85453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74108, d85453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74109 q = 1) (hb : d85454 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74109, d85454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74109, d85454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17849 (p : Pattern) (ha : d74115 p = 1) (hb : d85460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7303 q = 1) (hb : d52084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7303, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7303, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17835 q ha hb
  have h2 (q : Pattern) (ha : d7304 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7304, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7304, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7310 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17835 q ha hb
    | true =>
      simp only [d7310, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17836 q ha hb
  have h4 (q : Pattern) (ha : d7311 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7311, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7312 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7312, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7312, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74088 q = 1) (hb : d85438 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74088, d85438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17841 q ha hb
    | true =>
      simp only [d74088, d85438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17845 q ha hb
  have h7 (q : Pattern) (ha : d7377 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7377, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17837 q ha hb
    | true =>
      simp only [d7377, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h8 (q : Pattern) (ha : d74089 q = 1) (hb : d85439 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74089, d85439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74089, d85439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d74090 q = 1) (hb : d85440 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74090, d85440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74090, d85440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74091 q = 1) (hb : d85441 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74091, d85441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74091, d85441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74095 q = 1) (hb : d85445 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74095, d85445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74095, d85445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17846 q ha hb
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
  have h13 (q : Pattern) (ha : d74096 q = 1) (hb : d85446 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74096, d85446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74096, d85446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74097 q = 1) (hb : d85447 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74097, d85447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74097, d85447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74098 q = 1) (hb : d85448 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74098, d85448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74098, d85448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74099 q = 1) (hb : d85449 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74099, d85449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74099, d85449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74110 q = 1) (hb : d85455 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74110, d85455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74110, d85455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17848 q ha hb
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
  have h19 (q : Pattern) (ha : d74111 q = 1) (hb : d85456 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74111, d85456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74111, d85456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d74112 q = 1) (hb : d85457 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74112, d85457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74112, d85457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74113 q = 1) (hb : d85458 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74113, d85458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74113, d85458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74114 q = 1) (hb : d85459 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74114, d85459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74114, d85459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74115 q = 1) (hb : d85460 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74115, d85460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74115, d85460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17850 (p : Pattern) (ha : d74121 p = 1) (hb : d85466 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d52074 q = 1) (hb : d85423 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d85423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52074, d85423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17834 q ha hb
  have h6 (q : Pattern) (ha : d52075 q = 1) (hb : d85424 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d85424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52075, d85424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52076 q = 1) (hb : d85425 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d85425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52076, d85425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52077 q = 1) (hb : d85426 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d85426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52077, d85426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52078 q = 1) (hb : d85427 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d85427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52078, d85427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74116 q = 1) (hb : d85461 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74116, d85461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74116, d85461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17849 q ha hb
  have h11 (q : Pattern) (ha : d74117 q = 1) (hb : d85462 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74117, d85462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74117, d85462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74118 q = 1) (hb : d85463 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74118, d85463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74118, d85463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74119 q = 1) (hb : d85464 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74119, d85464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74119, d85464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74120 q = 1) (hb : d85465 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74120, d85465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74120, d85465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74121 q = 1) (hb : d85466 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74121, d85466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74121, d85466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17851 (p : Pattern) (ha : d7433 p = 1) (hb : d52234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7432 q = 1) (hb : d52233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7432, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7433 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7433, d52234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7433, d52234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17852 (p : Pattern) (ha : d7439 p = 1) (hb : d52244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7434 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17851 q ha hb
    | true =>
      simp only [d7434, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d7435 q = 1) (hb : d52240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7436 q = 1) (hb : d52241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7436, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7437 q = 1) (hb : d52242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7438 q = 1) (hb : d52243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7439 q = 1) (hb : d52244 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7439, d52244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7439, d52244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17853 (p : Pattern) (ha : d7442 p = 1) (hb : d52247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7432 q = 1) (hb : d52233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7432, d52233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7442 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7442, d52247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7442, d52247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17854 (p : Pattern) (ha : d7448 p = 1) (hb : d52254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7434 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17851 q ha hb
    | true =>
      simp only [d7434, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d7435 q = 1) (hb : d52240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7436 q = 1) (hb : d52241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7436, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7437 q = 1) (hb : d52242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7438 q = 1) (hb : d52243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7443 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17853 q ha hb
    | true =>
      simp only [d7443, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h7 (q : Pattern) (ha : d7444 q = 1) (hb : d52250 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d52250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7444, d52250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7445 q = 1) (hb : d52251 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d52251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7445, d52251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7446 q = 1) (hb : d52252 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d52252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d52252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7447 q = 1) (hb : d52253 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d52253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d52253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7448 q = 1) (hb : d52254 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7448, d52254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7448, d52254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17855 (p : Pattern) (ha : d7515 p = 1) (hb : d52342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7434 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17851 q ha hb
    | true =>
      simp only [d7434, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d7435 q = 1) (hb : d52240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d52240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7436 q = 1) (hb : d52241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7436, d52241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7437 q = 1) (hb : d52242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d52242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7438 q = 1) (hb : d52243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d52243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d52337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
    | true =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d52338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d52339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d52340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7515 q = 1) (hb : d52342 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7515, d52342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7515, d52342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17856 (p : Pattern) (ha : d7453 p = 1) (hb : d52259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7452 q = 1) (hb : d52258 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d52258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d52258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7453 q = 1) (hb : d52259 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7453, d52259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7453, d52259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17857 (p : Pattern) (ha : d7460 p = 1) (hb : d52268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7458 q = 1) (hb : d52266 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d52266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d52266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7459 q = 1) (hb : d52267 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d52267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7459, d52267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7460 q = 1) (hb : d52268 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7460, d52268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7460, d52268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17858 (p : Pattern) (ha : d7471 p = 1) (hb : d52307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7466 q = 1) (hb : d52302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11737 q ha hb
    | true =>
      simp only [d7466, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7467 q = 1) (hb : d52303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7467, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7468 q = 1) (hb : d52304 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d52304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7468, d52304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7469 q = 1) (hb : d52305 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d52305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7469, d52305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7470 q = 1) (hb : d52306 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d52306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7470, d52306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7471 q = 1) (hb : d52307 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7471, d52307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7471, d52307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17859 (p : Pattern) (ha : d74131 p = 1) (hb : d85471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7454 q = 1) (hb : d52262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17856 q ha hb
    | true =>
      simp only [d7454, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q ha hb
  have h2 (q : Pattern) (ha : d7455 q = 1) (hb : d52263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7456 q = 1) (hb : d52264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7456, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7457 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7461 q = 1) (hb : d52272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17857 q ha hb
    | true =>
      simp only [d7461, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h6 (q : Pattern) (ha : d7462 q = 1) (hb : d52273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7463 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7463, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7472 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17858 q ha hb
    | true =>
      simp only [d7472, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17851 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52309 q = 1) (hb : d85467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52309, d85467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52309, d85467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7487 q = 1) (hb : d74126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11734 q ha hb
    | true =>
      simp only [d7487, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7488 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7488, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74128 q = 1) (hb : d85468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74128, d85468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74128, d85468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74129 q = 1) (hb : d85469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74129, d85469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74129, d85469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74130 q = 1) (hb : d85470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74130, d85470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74130, d85470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74131 q = 1) (hb : d85471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74131, d85471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74131, d85471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17860 (p : Pattern) (ha : d7493 p = 1) (hb : d52316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d52232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d52232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7452 q = 1) (hb : d52258 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d52258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d52258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7493 q = 1) (hb : d52316 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7493, d52316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7493, d52316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17861 (p : Pattern) (ha : d7498 p = 1) (hb : d52322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d52231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d52231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7458 q = 1) (hb : d52266 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d52266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d52266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7459 q = 1) (hb : d52267 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d52267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7459, d52267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7498 q = 1) (hb : d52322 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7498, d52322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7498, d52322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17862 (p : Pattern) (ha : d7502 p = 1) (hb : d52327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7466 q = 1) (hb : d52302 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11737 q ha hb
    | true =>
      simp only [d7466, d52302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7467 q = 1) (hb : d52303 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7467, d52303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7327 q = 1) (hb : d52225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11728 q ha hb
    | true =>
      simp only [d7327, d52225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7328 q = 1) (hb : d52226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d52226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7468 q = 1) (hb : d52304 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d52304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7468, d52304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7469 q = 1) (hb : d52305 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d52305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7469, d52305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7470 q = 1) (hb : d52306 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d52306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7470, d52306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7502 q = 1) (hb : d52327 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7502, d52327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7502, d52327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17863 (p : Pattern) (ha : d74138 p = 1) (hb : d85476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7454 q = 1) (hb : d52262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17856 q ha hb
    | true =>
      simp only [d7454, d52262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q ha hb
  have h2 (q : Pattern) (ha : d7455 q = 1) (hb : d52263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d52263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7456 q = 1) (hb : d52264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7456, d52264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7457 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d52265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7461 q = 1) (hb : d52272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17857 q ha hb
    | true =>
      simp only [d7461, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h6 (q : Pattern) (ha : d7462 q = 1) (hb : d52273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7463 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7463, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7472 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17858 q ha hb
    | true =>
      simp only [d7472, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17851 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52309 q = 1) (hb : d85467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52309, d85467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52309, d85467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7487 q = 1) (hb : d74126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11734 q ha hb
    | true =>
      simp only [d7487, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7488 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7488, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74128 q = 1) (hb : d85468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74128, d85468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74128, d85468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74129 q = 1) (hb : d85469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74129, d85469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74129, d85469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74130 q = 1) (hb : d85470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74130, d85470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74130, d85470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7494 q = 1) (hb : d52318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7494, d52318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17860 q ha hb
    | true =>
      simp only [d7494, d52318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94 q ha hb
  have h17 (q : Pattern) (ha : d7495 q = 1) (hb : d52319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7495, d52319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7495, d52319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7496 q = 1) (hb : d52320 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7496, d52320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d7496, d52320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d7497 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7497, d52321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7497, d52321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7499 q = 1) (hb : d52324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7499, d52324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17861 q ha hb
    | true =>
      simp only [d7499, d52324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96 q ha hb
  have h21 (q : Pattern) (ha : d7500 q = 1) (hb : d52325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7500, d52325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7500, d52325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7501 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7501, d52326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7501, d52326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d7503 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17862 q ha hb
    | true =>
      simp only [d7503, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17853 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52329 q = 1) (hb : d85472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52329, d85472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d52329, d85472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7508 q = 1) (hb : d74133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11740 q ha hb
    | true =>
      simp only [d7508, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d7509 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7509, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74135 q = 1) (hb : d85473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74135, d85473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74135, d85473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74136 q = 1) (hb : d85474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74136, d85474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d74136, d85474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74137 q = 1) (hb : d85475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74137, d85475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d74137, d85475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74138 q = 1) (hb : d85476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74138, d85476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74138, d85476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17864 (p : Pattern) (ha : d74145 p = 1) (hb : d85483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7503 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17862 q ha hb
    | true =>
      simp only [d7503, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17853 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52329 q = 1) (hb : d85472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52329, d85472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52329, d85472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7508 q = 1) (hb : d74133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11740 q ha hb
    | true =>
      simp only [d7508, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7509 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7509, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74135 q = 1) (hb : d85473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74135, d85473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74135, d85473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74143 q = 1) (hb : d85481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74143, d85481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74143, d85481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74144 q = 1) (hb : d85482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74144, d85482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74144, d85482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74145 q = 1) (hb : d85483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74145, d85483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74145, d85483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17865 (p : Pattern) (ha : d7535 p = 1) (hb : d52385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7530 q = 1) (hb : d52375 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7530, d52375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11749 q ha hb
    | true =>
      simp only [d7530, d52375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7531 q = 1) (hb : d52376 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7531, d52376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7531, d52376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7391 q = 1) (hb : d52380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11746 q ha hb
    | true =>
      simp only [d7391, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7392 q = 1) (hb : d52381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7532 q = 1) (hb : d52382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7532, d52382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7532, d52382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7533 q = 1) (hb : d52383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7533, d52383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7533, d52383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7534 q = 1) (hb : d52384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7534, d52384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7534, d52384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7535 q = 1) (hb : d52385 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7535, d52385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7535, d52385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17866 (p : Pattern) (ha : d7539 p = 1) (hb : d52393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d52380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11746 q ha hb
    | true =>
      simp only [d7391, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d52381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71 q ha hb
    | true =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7536 q = 1) (hb : d52390 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7536, d52390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7536, d52390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7537 q = 1) (hb : d52391 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7537, d52391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7537, d52391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7538 q = 1) (hb : d52392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7538, d52392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7538, d52392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7539 q = 1) (hb : d52393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7539, d52393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7539, d52393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17867 (p : Pattern) (ha : d74160 p = 1) (hb : d85493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7540 q = 1) (hb : d52394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7540, d52394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17865 q ha hb
    | true =>
      simp only [d7540, d52394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17866 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52399 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52400 q = 1) (hb : d85489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52400, d85489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52400, d85489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7555 q = 1) (hb : d74155 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7555, d74155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11748 q ha hb
    | true =>
      simp only [d7555, d74155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7556 q = 1) (hb : d74156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7556, d74156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7556, d74156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74157 q = 1) (hb : d85490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74157, d85490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74157, d85490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74158 q = 1) (hb : d85491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74158, d85491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74158, d85491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74159 q = 1) (hb : d85492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74159, d85492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74159, d85492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74160 q = 1) (hb : d85493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74160, d85493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74160, d85493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17868 (p : Pattern) (ha : d74166 p = 1) (hb : d85499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7440 q = 1) (hb : d52245 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7440, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7440, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17852 q ha hb
  have h2 (q : Pattern) (ha : d7441 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7441, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7441, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7449 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17852 q ha hb
    | true =>
      simp only [d7449, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17854 q ha hb
  have h4 (q : Pattern) (ha : d7450 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7450, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7451 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7451, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7451, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74139 q = 1) (hb : d85477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74139, d85477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17859 q ha hb
    | true =>
      simp only [d74139, d85477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17863 q ha hb
  have h7 (q : Pattern) (ha : d7516 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7516, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17855 q ha hb
    | true =>
      simp only [d7516, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69 q ha hb
  have h8 (q : Pattern) (ha : d74140 q = 1) (hb : d85478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74140, d85478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74140, d85478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d74141 q = 1) (hb : d85479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74141, d85479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74141, d85479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74142 q = 1) (hb : d85480 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74142, d85480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74142, d85480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74146 q = 1) (hb : d85484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74146, d85484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74146, d85484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17864 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70 q ha hb
  have h13 (q : Pattern) (ha : d74147 q = 1) (hb : d85485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74147, d85485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74147, d85485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74148 q = 1) (hb : d85486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74148, d85486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74148, d85486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74149 q = 1) (hb : d85487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74149, d85487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74149, d85487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74150 q = 1) (hb : d85488 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74150, d85488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74150, d85488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74161 q = 1) (hb : d85494 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74161, d85494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74161, d85494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17867 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73 q ha hb
  have h19 (q : Pattern) (ha : d74162 q = 1) (hb : d85495 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74162, d85495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74162, d85495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d74163 q = 1) (hb : d85496 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74163, d85496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74163, d85496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74164 q = 1) (hb : d85497 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74164, d85497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74164, d85497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74165 q = 1) (hb : d85498 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74165, d85498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74165, d85498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74166 q = 1) (hb : d85499 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74166, d85499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74166, d85499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17869 (p : Pattern) (ha : d74172 p = 1) (hb : d85505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74167 q = 1) (hb : d85500 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74167, d85500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74167, d85500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17868 q ha hb
  have h2 (q : Pattern) (ha : d74168 q = 1) (hb : d85501 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74168, d85501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74168, d85501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74169 q = 1) (hb : d85502 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74169, d85502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74169, d85502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74170 q = 1) (hb : d85503 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74170, d85503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74170, d85503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74171 q = 1) (hb : d85504 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74171, d85504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74171, d85504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74172 q = 1) (hb : d85505 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74172, d85505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74172, d85505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17870 (p : Pattern) (ha : d7581 p = 1) (hb : d52456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11754 q ha hb
    | true =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d52454 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7580 q = 1) (hb : d52455 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d52455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7580, d52455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7581 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7581, d52456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7581, d52456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17871 (p : Pattern) (ha : d7587 p = 1) (hb : d52466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7582 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17870 q ha hb
    | true =>
      simp only [d7582, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d7583 q = 1) (hb : d52462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7584 q = 1) (hb : d52463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7584, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7585 q = 1) (hb : d52464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7586 q = 1) (hb : d52465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7587 q = 1) (hb : d52466 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7587, d52466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7587, d52466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17872 (p : Pattern) (ha : d7590 p = 1) (hb : d52469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11754 q ha hb
    | true =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d52454 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7580 q = 1) (hb : d52455 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d52455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7580, d52455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7590 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7590, d52469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7590, d52469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17873 (p : Pattern) (ha : d7596 p = 1) (hb : d52476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7582 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17870 q ha hb
    | true =>
      simp only [d7582, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d7583 q = 1) (hb : d52462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7584 q = 1) (hb : d52463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7584, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7585 q = 1) (hb : d52464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7586 q = 1) (hb : d52465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7591 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17872 q ha hb
    | true =>
      simp only [d7591, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h7 (q : Pattern) (ha : d7592 q = 1) (hb : d52472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d52472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7592, d52472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7593 q = 1) (hb : d52473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d52473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7593, d52473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7594 q = 1) (hb : d52474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d52474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d52474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7595 q = 1) (hb : d52475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d52475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d52475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7596 q = 1) (hb : d52476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7596, d52476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7596, d52476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17874 (p : Pattern) (ha : d7663 p = 1) (hb : d52563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7582 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17870 q ha hb
    | true =>
      simp only [d7582, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d7583 q = 1) (hb : d52462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7584 q = 1) (hb : d52463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7584, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7585 q = 1) (hb : d52464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7586 q = 1) (hb : d52465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d52558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
    | true =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d52559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d52560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d52561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7663 q = 1) (hb : d52563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7663, d52563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7663, d52563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17875 (p : Pattern) (ha : d7601 p = 1) (hb : d52481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11754 q ha hb
    | true =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d52454 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7600 q = 1) (hb : d52480 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d52480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d52480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7601 q = 1) (hb : d52481 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7601, d52481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7601, d52481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17876 (p : Pattern) (ha : d7608 p = 1) (hb : d52490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11754 q ha hb
    | true =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7606 q = 1) (hb : d52488 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d52488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d52488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7607 q = 1) (hb : d52489 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d52489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7607, d52489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7608 q = 1) (hb : d52490 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7608, d52490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7608, d52490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17877 (p : Pattern) (ha : d7619 p = 1) (hb : d52528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7614 q = 1) (hb : d52523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11764 q ha hb
    | true =>
      simp only [d7614, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7615 q = 1) (hb : d52524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7615, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7576 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11754 q ha hb
    | true =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7577 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7616 q = 1) (hb : d52525 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d52525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7616, d52525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7617 q = 1) (hb : d52526 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d52526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7617, d52526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7618 q = 1) (hb : d52527 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d52527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7618, d52527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7619 q = 1) (hb : d52528 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7619, d52528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7619, d52528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17878 (p : Pattern) (ha : d74201 p = 1) (hb : d85511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7602 q = 1) (hb : d52484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17875 q ha hb
    | true =>
      simp only [d7602, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q ha hb
  have h2 (q : Pattern) (ha : d7603 q = 1) (hb : d52485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7604 q = 1) (hb : d52486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7604, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7605 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7609 q = 1) (hb : d52494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17876 q ha hb
    | true =>
      simp only [d7609, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h6 (q : Pattern) (ha : d7610 q = 1) (hb : d52495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7611 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7611, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7620 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17877 q ha hb
    | true =>
      simp only [d7620, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17870 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52530 q = 1) (hb : d85507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52530, d85507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52530, d85507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7635 q = 1) (hb : d74196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d74196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11761 q ha hb
    | true =>
      simp only [d7635, d74196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7636 q = 1) (hb : d74197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, d74197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7636, d74197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74198 q = 1) (hb : d85508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74198, d85508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74198, d85508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74199 q = 1) (hb : d85509 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74199, d85509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74199, d85509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74200 q = 1) (hb : d85510 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74200, d85510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74200, d85510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74201 q = 1) (hb : d85511 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74201, d85511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74201, d85511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17879 (p : Pattern) (ha : d7641 p = 1) (hb : d52537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11754 q ha hb
    | true =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d52454 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d52454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7600 q = 1) (hb : d52480 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d52480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d52480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7641 q = 1) (hb : d52537 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7641, d52537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7641, d52537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17880 (p : Pattern) (ha : d7646 p = 1) (hb : d52543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11754 q ha hb
    | true =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d52453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d52453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7606 q = 1) (hb : d52488 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d52488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d52488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7607 q = 1) (hb : d52489 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d52489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7607, d52489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7646 q = 1) (hb : d52543 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7646, d52543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7646, d52543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17881 (p : Pattern) (ha : d7650 p = 1) (hb : d52548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7614 q = 1) (hb : d52523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11764 q ha hb
    | true =>
      simp only [d7614, d52523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7615 q = 1) (hb : d52524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7615, d52524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7576 q = 1) (hb : d52447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11754 q ha hb
    | true =>
      simp only [d7576, d52447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7577 q = 1) (hb : d52448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d52448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7616 q = 1) (hb : d52525 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d52525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7616, d52525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7617 q = 1) (hb : d52526 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d52526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7617, d52526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7618 q = 1) (hb : d52527 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d52527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7618, d52527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7650 q = 1) (hb : d52548 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7650, d52548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7650, d52548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17882 (p : Pattern) (ha : d74208 p = 1) (hb : d85516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7602 q = 1) (hb : d52484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17875 q ha hb
    | true =>
      simp only [d7602, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q ha hb
  have h2 (q : Pattern) (ha : d7603 q = 1) (hb : d52485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7604 q = 1) (hb : d52486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7604, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7605 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7609 q = 1) (hb : d52494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17876 q ha hb
    | true =>
      simp only [d7609, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h6 (q : Pattern) (ha : d7610 q = 1) (hb : d52495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7611 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7611, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7620 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17877 q ha hb
    | true =>
      simp only [d7620, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17870 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52530 q = 1) (hb : d85507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52530, d85507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52530, d85507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7635 q = 1) (hb : d74196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d74196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11761 q ha hb
    | true =>
      simp only [d7635, d74196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7636 q = 1) (hb : d74197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, d74197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7636, d74197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74198 q = 1) (hb : d85508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74198, d85508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74198, d85508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74199 q = 1) (hb : d85509 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74199, d85509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74199, d85509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74200 q = 1) (hb : d85510 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74200, d85510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74200, d85510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7642 q = 1) (hb : d52539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7642, d52539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17879 q ha hb
    | true =>
      simp only [d7642, d52539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro141 q ha hb
  have h17 (q : Pattern) (ha : d7643 q = 1) (hb : d52540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7643, d52540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7643, d52540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7644 q = 1) (hb : d52541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7644, d52541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d7644, d52541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d7645 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7645, d52542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7645, d52542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7647 q = 1) (hb : d52545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7647, d52545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17880 q ha hb
    | true =>
      simp only [d7647, d52545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro143 q ha hb
  have h21 (q : Pattern) (ha : d7648 q = 1) (hb : d52546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7648, d52546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7648, d52546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7649 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7649, d52547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7649, d52547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d7651 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17881 q ha hb
    | true =>
      simp only [d7651, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17872 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52550 q = 1) (hb : d85512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52550, d85512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d52550, d85512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7656 q = 1) (hb : d74203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d74203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11767 q ha hb
    | true =>
      simp only [d7656, d74203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d7657 q = 1) (hb : d74204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, d74204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7657, d74204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74205 q = 1) (hb : d85513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74205, d85513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74205, d85513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74206 q = 1) (hb : d85514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74206, d85514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d74206, d85514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74207 q = 1) (hb : d85515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74207, d85515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d74207, d85515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74208 q = 1) (hb : d85516 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74208, d85516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74208, d85516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17883 (p : Pattern) (ha : d74215 p = 1) (hb : d85523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7651 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17881 q ha hb
    | true =>
      simp only [d7651, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17872 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52550 q = 1) (hb : d85512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52550, d85512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52550, d85512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7656 q = 1) (hb : d74203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d74203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11767 q ha hb
    | true =>
      simp only [d7656, d74203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7657 q = 1) (hb : d74204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, d74204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7657, d74204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74205 q = 1) (hb : d85513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74205, d85513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74205, d85513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74213 q = 1) (hb : d85521 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74213, d85521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74213, d85521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74214 q = 1) (hb : d85522 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74214, d85522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74214, d85522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74215 q = 1) (hb : d85523 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74215, d85523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74215, d85523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17884 (p : Pattern) (ha : d7687 p = 1) (hb : d52622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7678 q = 1) (hb : d52612 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7678, d52612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11777 q ha hb
    | true =>
      simp only [d7678, d52612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7679 q = 1) (hb : d52613 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7679, d52613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7679, d52613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7682 q = 1) (hb : d52617 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11773 q ha hb
    | true =>
      simp only [d7682, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7683 q = 1) (hb : d52618 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7683, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7684 q = 1) (hb : d52619 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7684, d52619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7684, d52619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7685 q = 1) (hb : d52620 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7685, d52620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7685, d52620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7686 q = 1) (hb : d52621 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7686, d52621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7686, d52621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7687 q = 1) (hb : d52622 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7687, d52622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7687, d52622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17885 (p : Pattern) (ha : d7691 p = 1) (hb : d52630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7682 q = 1) (hb : d52617 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11773 q ha hb
    | true =>
      simp only [d7682, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7683 q = 1) (hb : d52618 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7683, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro117 q ha hb
    | true =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7688 q = 1) (hb : d52627 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7688, d52627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7688, d52627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7689 q = 1) (hb : d52628 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7689, d52628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7689, d52628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7690 q = 1) (hb : d52629 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7690, d52629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7690, d52629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7691 q = 1) (hb : d52630 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7691, d52630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7691, d52630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17886 (p : Pattern) (ha : d74245 p = 1) (hb : d85533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7692 q = 1) (hb : d52631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7692, d52631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17884 q ha hb
    | true =>
      simp only [d7692, d52631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17885 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52636 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52637 q = 1) (hb : d85529 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52637, d85529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52637, d85529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7707 q = 1) (hb : d74240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7707, d74240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11776 q ha hb
    | true =>
      simp only [d7707, d74240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7708 q = 1) (hb : d74241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7708, d74241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7708, d74241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74242 q = 1) (hb : d85530 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74242, d85530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74242, d85530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74243 q = 1) (hb : d85531 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74243, d85531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74243, d85531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74244 q = 1) (hb : d85532 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74244, d85532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74244, d85532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74245 q = 1) (hb : d85533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74245, d85533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74245, d85533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17887 (p : Pattern) (ha : d74251 p = 1) (hb : d85539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7588 q = 1) (hb : d52467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7588, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7588, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17871 q ha hb
  have h2 (q : Pattern) (ha : d7589 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7589, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7589, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7597 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17871 q ha hb
    | true =>
      simp only [d7597, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17873 q ha hb
  have h4 (q : Pattern) (ha : d7598 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7598, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7599 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7599, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7599, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74209 q = 1) (hb : d85517 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74209, d85517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17878 q ha hb
    | true =>
      simp only [d74209, d85517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17882 q ha hb
  have h7 (q : Pattern) (ha : d7664 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7664, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17874 q ha hb
    | true =>
      simp only [d7664, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro113 q ha hb
  have h8 (q : Pattern) (ha : d74210 q = 1) (hb : d85518 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74210, d85518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74210, d85518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d74211 q = 1) (hb : d85519 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74211, d85519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74211, d85519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74212 q = 1) (hb : d85520 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74212, d85520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74212, d85520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74216 q = 1) (hb : d85524 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74216, d85524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74216, d85524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17883 q ha hb
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
  have h13 (q : Pattern) (ha : d74217 q = 1) (hb : d85525 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74217, d85525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74217, d85525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74218 q = 1) (hb : d85526 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74218, d85526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74218, d85526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74219 q = 1) (hb : d85527 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74219, d85527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74219, d85527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74220 q = 1) (hb : d85528 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74220, d85528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74220, d85528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74246 q = 1) (hb : d85534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74246, d85534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74246, d85534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17886 q ha hb
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
  have h19 (q : Pattern) (ha : d74247 q = 1) (hb : d85535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74247, d85535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74247, d85535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d74248 q = 1) (hb : d85536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74248, d85536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74248, d85536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74249 q = 1) (hb : d85537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74249, d85537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74249, d85537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74250 q = 1) (hb : d85538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74250, d85538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74250, d85538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74251 q = 1) (hb : d85539 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74251, d85539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74251, d85539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17888 (p : Pattern) (ha : d74257 p = 1) (hb : d85545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74252 q = 1) (hb : d85540 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74252, d85540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74252, d85540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17887 q ha hb
  have h2 (q : Pattern) (ha : d74253 q = 1) (hb : d85541 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74253, d85541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74253, d85541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74254 q = 1) (hb : d85542 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74254, d85542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74254, d85542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74255 q = 1) (hb : d85543 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74255, d85543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74255, d85543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74256 q = 1) (hb : d85544 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74256, d85544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74256, d85544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74257 q = 1) (hb : d85545 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74257, d85545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74257, d85545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17889 (p : Pattern) (ha : d7734 p = 1) (hb : d52739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11782 q ha hb
    | true =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7733 q = 1) (hb : d52738 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7733, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7734 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7734, d52739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7734, d52739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17890 (p : Pattern) (ha : d7740 p = 1) (hb : d52749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7735 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17889 q ha hb
    | true =>
      simp only [d7735, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d7736 q = 1) (hb : d52745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7737 q = 1) (hb : d52746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7737, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7738 q = 1) (hb : d52747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7739 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7740 q = 1) (hb : d52749 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7740, d52749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7740, d52749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17891 (p : Pattern) (ha : d7743 p = 1) (hb : d52752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11782 q ha hb
    | true =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7733 q = 1) (hb : d52738 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7733, d52738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7743 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7743, d52752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7743, d52752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17892 (p : Pattern) (ha : d7749 p = 1) (hb : d52759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7735 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17889 q ha hb
    | true =>
      simp only [d7735, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d7736 q = 1) (hb : d52745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7737 q = 1) (hb : d52746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7737, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7738 q = 1) (hb : d52747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7739 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7744 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17891 q ha hb
    | true =>
      simp only [d7744, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h7 (q : Pattern) (ha : d7745 q = 1) (hb : d52755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d52755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7745, d52755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7746 q = 1) (hb : d52756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d52756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7746, d52756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7747 q = 1) (hb : d52757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d52757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d52757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7748 q = 1) (hb : d52758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d52758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d52758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7749 q = 1) (hb : d52759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7749, d52759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7749, d52759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17893 (p : Pattern) (ha : d7816 p = 1) (hb : d52843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7735 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17889 q ha hb
    | true =>
      simp only [d7735, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d7736 q = 1) (hb : d52745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7737 q = 1) (hb : d52746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7737, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7738 q = 1) (hb : d52747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7739 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d52838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
    | true =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d52839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d52840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d52841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7816 q = 1) (hb : d52843 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7816, d52843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7816, d52843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17894 (p : Pattern) (ha : d7754 p = 1) (hb : d52764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11782 q ha hb
    | true =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7753 q = 1) (hb : d52763 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7754 q = 1) (hb : d52764 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7754, d52764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7754, d52764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17895 (p : Pattern) (ha : d7761 p = 1) (hb : d52773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11782 q ha hb
    | true =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7759 q = 1) (hb : d52771 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7760 q = 1) (hb : d52772 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7760, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7761 q = 1) (hb : d52773 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7761, d52773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7761, d52773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17896 (p : Pattern) (ha : d7772 p = 1) (hb : d52808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7767 q = 1) (hb : d52803 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11792 q ha hb
    | true =>
      simp only [d7767, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7768 q = 1) (hb : d52804 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7768, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7729 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11782 q ha hb
    | true =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7730 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7769 q = 1) (hb : d52805 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d52805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7769, d52805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7770 q = 1) (hb : d52806 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d52806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7770, d52806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7771 q = 1) (hb : d52807 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d52807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7771, d52807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7772 q = 1) (hb : d52808 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7772, d52808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7772, d52808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17897 (p : Pattern) (ha : d74290 p = 1) (hb : d85552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7755 q = 1) (hb : d52767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17894 q ha hb
    | true =>
      simp only [d7755, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d7756 q = 1) (hb : d52768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7757 q = 1) (hb : d52769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7757, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7758 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7762 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17895 q ha hb
    | true =>
      simp only [d7762, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d7763 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7764 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7764, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7773 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17896 q ha hb
    | true =>
      simp only [d7773, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17889 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52810 q = 1) (hb : d85548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52810, d85548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52810, d85548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7788 q = 1) (hb : d74285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d74285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11789 q ha hb
    | true =>
      simp only [d7788, d74285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7789 q = 1) (hb : d74286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, d74286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7789, d74286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74287 q = 1) (hb : d85549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74287, d85549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74287, d85549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74288 q = 1) (hb : d85550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74288, d85550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74288, d85550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74289 q = 1) (hb : d85551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74289, d85551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74289, d85551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74290 q = 1) (hb : d85552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74290, d85552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74290, d85552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17898 (p : Pattern) (ha : d7794 p = 1) (hb : d52817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11782 q ha hb
    | true =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d52737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d52737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7753 q = 1) (hb : d52763 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d52763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7794 q = 1) (hb : d52817 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7794, d52817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7794, d52817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17899 (p : Pattern) (ha : d7799 p = 1) (hb : d52823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11782 q ha hb
    | true =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d52736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d52736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7759 q = 1) (hb : d52771 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d52771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7760 q = 1) (hb : d52772 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7760, d52772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7799 q = 1) (hb : d52823 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7799, d52823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7799, d52823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17900 (p : Pattern) (ha : d7803 p = 1) (hb : d52828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7767 q = 1) (hb : d52803 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11792 q ha hb
    | true =>
      simp only [d7767, d52803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7768 q = 1) (hb : d52804 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7768, d52804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7729 q = 1) (hb : d52730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11782 q ha hb
    | true =>
      simp only [d7729, d52730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7730 q = 1) (hb : d52731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d52731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7769 q = 1) (hb : d52805 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d52805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7769, d52805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7770 q = 1) (hb : d52806 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d52806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7770, d52806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7771 q = 1) (hb : d52807 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d52807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7771, d52807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7803 q = 1) (hb : d52828 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7803, d52828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7803, d52828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17901 (p : Pattern) (ha : d74297 p = 1) (hb : d85557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7755 q = 1) (hb : d52767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17894 q ha hb
    | true =>
      simp only [d7755, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d7756 q = 1) (hb : d52768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7757 q = 1) (hb : d52769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7757, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7758 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7762 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17895 q ha hb
    | true =>
      simp only [d7762, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d7763 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7764 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7764, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7773 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17896 q ha hb
    | true =>
      simp only [d7773, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17889 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52810 q = 1) (hb : d85548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52810, d85548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52810, d85548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7788 q = 1) (hb : d74285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d74285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11789 q ha hb
    | true =>
      simp only [d7788, d74285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7789 q = 1) (hb : d74286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, d74286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7789, d74286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74287 q = 1) (hb : d85549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74287, d85549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74287, d85549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74288 q = 1) (hb : d85550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74288, d85550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74288, d85550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74289 q = 1) (hb : d85551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74289, d85551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74289, d85551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7795 q = 1) (hb : d52819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7795, d52819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17898 q ha hb
    | true =>
      simp only [d7795, d52819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro193 q ha hb
  have h17 (q : Pattern) (ha : d7796 q = 1) (hb : d52820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7796, d52820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7796, d52820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7797 q = 1) (hb : d52821 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7797, d52821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d7797, d52821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d7798 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7798, d52822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7798, d52822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7800 q = 1) (hb : d52825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7800, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17899 q ha hb
    | true =>
      simp only [d7800, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro195 q ha hb
  have h21 (q : Pattern) (ha : d7801 q = 1) (hb : d52826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7801, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7801, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7802 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7802, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7802, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d7804 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17900 q ha hb
    | true =>
      simp only [d7804, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17891 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52830 q = 1) (hb : d85553 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52830, d85553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d52830, d85553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7809 q = 1) (hb : d74292 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d74292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11795 q ha hb
    | true =>
      simp only [d7809, d74292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d7810 q = 1) (hb : d74293 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, d74293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7810, d74293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74294 q = 1) (hb : d85554 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74294, d85554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74294, d85554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74295 q = 1) (hb : d85555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74295, d85555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d74295, d85555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74296 q = 1) (hb : d85556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74296, d85556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d74296, d85556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74297 q = 1) (hb : d85557 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74297, d85557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74297, d85557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17902 (p : Pattern) (ha : d74304 p = 1) (hb : d85564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7804 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17900 q ha hb
    | true =>
      simp only [d7804, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17891 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52830 q = 1) (hb : d85553 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52830, d85553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52830, d85553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7809 q = 1) (hb : d74292 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d74292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11795 q ha hb
    | true =>
      simp only [d7809, d74292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7810 q = 1) (hb : d74293 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, d74293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7810, d74293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74294 q = 1) (hb : d85554 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74294, d85554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74294, d85554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74302 q = 1) (hb : d85562 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74302, d85562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74302, d85562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74303 q = 1) (hb : d85563 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74303, d85563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74303, d85563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74304 q = 1) (hb : d85564 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74304, d85564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74304, d85564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17903 (p : Pattern) (ha : d7840 p = 1) (hb : d52916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7831 q = 1) (hb : d52906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7831, d52906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11805 q ha hb
    | true =>
      simp only [d7831, d52906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7832 q = 1) (hb : d52907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7832, d52907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7832, d52907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7835 q = 1) (hb : d52911 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11801 q ha hb
    | true =>
      simp only [d7835, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7836 q = 1) (hb : d52912 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7836, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7837 q = 1) (hb : d52913 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7837, d52913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7837, d52913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7838 q = 1) (hb : d52914 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7838, d52914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7838, d52914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7839 q = 1) (hb : d52915 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7839, d52915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7839, d52915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7840 q = 1) (hb : d52916 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7840, d52916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7840, d52916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17904 (p : Pattern) (ha : d7844 p = 1) (hb : d52924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7835 q = 1) (hb : d52911 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11801 q ha hb
    | true =>
      simp only [d7835, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7836 q = 1) (hb : d52912 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7836, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d52919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro169 q ha hb
    | true =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7841 q = 1) (hb : d52921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7841, d52921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7841, d52921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7842 q = 1) (hb : d52922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7842, d52922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7842, d52922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7843 q = 1) (hb : d52923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7843, d52923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7843, d52923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7844 q = 1) (hb : d52924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7844, d52924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7844, d52924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17905 (p : Pattern) (ha : d74334 p = 1) (hb : d85574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7845 q = 1) (hb : d52925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7845, d52925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17903 q ha hb
    | true =>
      simp only [d7845, d52925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17904 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52930 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52931 q = 1) (hb : d85570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52931, d85570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52931, d85570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7860 q = 1) (hb : d74329 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7860, d74329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11804 q ha hb
    | true =>
      simp only [d7860, d74329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7861 q = 1) (hb : d74330 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7861, d74330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7861, d74330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74331 q = 1) (hb : d85571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74331, d85571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74331, d85571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74332 q = 1) (hb : d85572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74332, d85572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74332, d85572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74333 q = 1) (hb : d85573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74333, d85573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74333, d85573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74334 q = 1) (hb : d85574 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74334, d85574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74334, d85574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17906 (p : Pattern) (ha : d74340 p = 1) (hb : d85580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7741 q = 1) (hb : d52750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7741, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7741, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17890 q ha hb
  have h2 (q : Pattern) (ha : d7742 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7742, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7742, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7750 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17890 q ha hb
    | true =>
      simp only [d7750, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17892 q ha hb
  have h4 (q : Pattern) (ha : d7751 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7751, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7752 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7752, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7752, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74298 q = 1) (hb : d85558 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74298, d85558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17897 q ha hb
    | true =>
      simp only [d74298, d85558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17901 q ha hb
  have h7 (q : Pattern) (ha : d7817 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7817, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17893 q ha hb
    | true =>
      simp only [d7817, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro165 q ha hb
  have h8 (q : Pattern) (ha : d74299 q = 1) (hb : d85559 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74299, d85559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74299, d85559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d74300 q = 1) (hb : d85560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74300, d85560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74300, d85560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74301 q = 1) (hb : d85561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74301, d85561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74301, d85561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74305 q = 1) (hb : d85565 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74305, d85565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74305, d85565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17902 q ha hb
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
  have h13 (q : Pattern) (ha : d74306 q = 1) (hb : d85566 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74306, d85566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74306, d85566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74307 q = 1) (hb : d85567 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74307, d85567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74307, d85567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74308 q = 1) (hb : d85568 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74308, d85568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74308, d85568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74309 q = 1) (hb : d85569 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74309, d85569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74309, d85569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74335 q = 1) (hb : d85575 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74335, d85575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74335, d85575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17905 q ha hb
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
  have h19 (q : Pattern) (ha : d74336 q = 1) (hb : d85576 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74336, d85576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74336, d85576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d74337 q = 1) (hb : d85577 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74337, d85577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74337, d85577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74338 q = 1) (hb : d85578 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74338, d85578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74338, d85578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74339 q = 1) (hb : d85579 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74339, d85579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74339, d85579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74340 q = 1) (hb : d85580 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74340, d85580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74340, d85580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17907 (p : Pattern) (ha : d74346 p = 1) (hb : d85586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74341 q = 1) (hb : d85581 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74341, d85581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74341, d85581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17906 q ha hb
  have h2 (q : Pattern) (ha : d74342 q = 1) (hb : d85582 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74342, d85582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74342, d85582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74343 q = 1) (hb : d85583 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74343, d85583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74343, d85583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74344 q = 1) (hb : d85584 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74344, d85584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74344, d85584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74345 q = 1) (hb : d85585 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74345, d85585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74345, d85585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74346 q = 1) (hb : d85586 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74346, d85586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74346, d85586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17908 (p : Pattern) (ha : d7888 p = 1) (hb : d53060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11810 q ha hb
    | true =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7887 q = 1) (hb : d53059 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7887, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7888 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7888, d53060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7888, d53060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17909 (p : Pattern) (ha : d7894 p = 1) (hb : d53070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7889 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17908 q ha hb
    | true =>
      simp only [d7889, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d7890 q = 1) (hb : d53066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7891 q = 1) (hb : d53067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7891, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7892 q = 1) (hb : d53068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7893 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7894 q = 1) (hb : d53070 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7894, d53070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7894, d53070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17910 (p : Pattern) (ha : d7897 p = 1) (hb : d53073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11810 q ha hb
    | true =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7887 q = 1) (hb : d53059 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7887, d53059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7897 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7897, d53073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7897, d53073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17911 (p : Pattern) (ha : d7903 p = 1) (hb : d53080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7889 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17908 q ha hb
    | true =>
      simp only [d7889, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d7890 q = 1) (hb : d53066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7891 q = 1) (hb : d53067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7891, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7892 q = 1) (hb : d53068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7893 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7898 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17910 q ha hb
    | true =>
      simp only [d7898, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h7 (q : Pattern) (ha : d7899 q = 1) (hb : d53076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d53076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7899, d53076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7900 q = 1) (hb : d53077 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d53077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7900, d53077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7901 q = 1) (hb : d53078 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d53078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d53078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7902 q = 1) (hb : d53079 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d53079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d53079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7903 q = 1) (hb : d53080 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7903, d53080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7903, d53080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17912 (p : Pattern) (ha : d7970 p = 1) (hb : d53158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7889 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17908 q ha hb
    | true =>
      simp only [d7889, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d7890 q = 1) (hb : d53066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7891 q = 1) (hb : d53067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7891, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7892 q = 1) (hb : d53068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7893 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d53153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
    | true =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d53154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d53155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d53156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7970 q = 1) (hb : d53158 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7970, d53158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7970, d53158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17913 (p : Pattern) (ha : d7908 p = 1) (hb : d53085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11810 q ha hb
    | true =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7907 q = 1) (hb : d53084 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7908 q = 1) (hb : d53085 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7908, d53085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7908, d53085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17914 (p : Pattern) (ha : d7915 p = 1) (hb : d53094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11810 q ha hb
    | true =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7913 q = 1) (hb : d53092 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7914 q = 1) (hb : d53093 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7914, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7915 q = 1) (hb : d53094 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7915, d53094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7915, d53094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17915 (p : Pattern) (ha : d7926 p = 1) (hb : d53123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7921 q = 1) (hb : d53118 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11820 q ha hb
    | true =>
      simp only [d7921, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7922 q = 1) (hb : d53119 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7922, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7883 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11810 q ha hb
    | true =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7884 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7923 q = 1) (hb : d53120 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d53120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7923, d53120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7924 q = 1) (hb : d53121 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d53121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7924, d53121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7925 q = 1) (hb : d53122 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d53122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7925, d53122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7926 q = 1) (hb : d53123 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7926, d53123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7926, d53123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17916 (p : Pattern) (ha : d74380 p = 1) (hb : d85594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7909 q = 1) (hb : d53088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17913 q ha hb
    | true =>
      simp only [d7909, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d7910 q = 1) (hb : d53089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7911 q = 1) (hb : d53090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7911, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7912 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7916 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17914 q ha hb
    | true =>
      simp only [d7916, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d7917 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7918 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7918, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7927 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17915 q ha hb
    | true =>
      simp only [d7927, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17908 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53125 q = 1) (hb : d85590 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53125, d85590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53125, d85590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7942 q = 1) (hb : d74375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d74375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11817 q ha hb
    | true =>
      simp only [d7942, d74375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7943 q = 1) (hb : d74376 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, d74376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7943, d74376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74377 q = 1) (hb : d85591 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74377, d85591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74377, d85591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74378 q = 1) (hb : d85592 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74378, d85592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74378, d85592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74379 q = 1) (hb : d85593 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74379, d85593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74379, d85593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74380 q = 1) (hb : d85594 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74380, d85594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74380, d85594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17917 (p : Pattern) (ha : d7948 p = 1) (hb : d53132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11810 q ha hb
    | true =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d53058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d53058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7907 q = 1) (hb : d53084 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d53084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7948 q = 1) (hb : d53132 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7948, d53132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7948, d53132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17918 (p : Pattern) (ha : d7953 p = 1) (hb : d53138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11810 q ha hb
    | true =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d53057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d53057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7913 q = 1) (hb : d53092 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d53092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7914 q = 1) (hb : d53093 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7914, d53093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7953 q = 1) (hb : d53138 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7953, d53138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7953, d53138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17919 (p : Pattern) (ha : d7957 p = 1) (hb : d53143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7921 q = 1) (hb : d53118 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11820 q ha hb
    | true =>
      simp only [d7921, d53118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7922 q = 1) (hb : d53119 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7922, d53119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7883 q = 1) (hb : d53051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11810 q ha hb
    | true =>
      simp only [d7883, d53051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7884 q = 1) (hb : d53052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d53052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7923 q = 1) (hb : d53120 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d53120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7923, d53120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7924 q = 1) (hb : d53121 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d53121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7924, d53121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7925 q = 1) (hb : d53122 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d53122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7925, d53122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7957 q = 1) (hb : d53143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7957, d53143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7957, d53143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17920 (p : Pattern) (ha : d74387 p = 1) (hb : d85599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7909 q = 1) (hb : d53088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17913 q ha hb
    | true =>
      simp only [d7909, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d7910 q = 1) (hb : d53089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7911 q = 1) (hb : d53090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7911, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7912 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7916 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17914 q ha hb
    | true =>
      simp only [d7916, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d7917 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7918 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7918, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7927 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17915 q ha hb
    | true =>
      simp only [d7927, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17908 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53125 q = 1) (hb : d85590 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53125, d85590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53125, d85590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7942 q = 1) (hb : d74375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d74375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11817 q ha hb
    | true =>
      simp only [d7942, d74375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7943 q = 1) (hb : d74376 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, d74376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7943, d74376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74377 q = 1) (hb : d85591 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74377, d85591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74377, d85591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74378 q = 1) (hb : d85592 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74378, d85592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74378, d85592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74379 q = 1) (hb : d85593 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74379, d85593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74379, d85593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7949 q = 1) (hb : d53134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7949, d53134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17917 q ha hb
    | true =>
      simp only [d7949, d53134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro249 q ha hb
  have h17 (q : Pattern) (ha : d7950 q = 1) (hb : d53135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7950, d53135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7950, d53135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7951 q = 1) (hb : d53136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7951, d53136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d7951, d53136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d7952 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7952, d53137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7952, d53137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7954 q = 1) (hb : d53140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7954, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17918 q ha hb
    | true =>
      simp only [d7954, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro251 q ha hb
  have h21 (q : Pattern) (ha : d7955 q = 1) (hb : d53141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7955, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7955, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7956 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7956, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7956, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d7958 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17919 q ha hb
    | true =>
      simp only [d7958, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17910 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d53145 q = 1) (hb : d85595 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53145, d85595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d53145, d85595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7963 q = 1) (hb : d74382 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d74382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11823 q ha hb
    | true =>
      simp only [d7963, d74382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d7964 q = 1) (hb : d74383 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, d74383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7964, d74383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74384 q = 1) (hb : d85596 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74384, d85596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74384, d85596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74385 q = 1) (hb : d85597 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74385, d85597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d74385, d85597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74386 q = 1) (hb : d85598 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74386, d85598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d74386, d85598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74387 q = 1) (hb : d85599 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74387, d85599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74387, d85599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17921 (p : Pattern) (ha : d74394 p = 1) (hb : d85606 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7958 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17919 q ha hb
    | true =>
      simp only [d7958, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17910 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53145 q = 1) (hb : d85595 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53145, d85595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53145, d85595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7963 q = 1) (hb : d74382 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d74382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11823 q ha hb
    | true =>
      simp only [d7963, d74382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7964 q = 1) (hb : d74383 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, d74383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7964, d74383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74384 q = 1) (hb : d85596 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74384, d85596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74384, d85596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74392 q = 1) (hb : d85604 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74392, d85604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74392, d85604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74393 q = 1) (hb : d85605 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74393, d85605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74393, d85605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74394 q = 1) (hb : d85606 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74394, d85606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74394, d85606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17922 (p : Pattern) (ha : d7994 p = 1) (hb : d53231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7985 q = 1) (hb : d53221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7985, d53221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11833 q ha hb
    | true =>
      simp only [d7985, d53221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7986 q = 1) (hb : d53222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7986, d53222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7986, d53222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7989 q = 1) (hb : d53226 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11829 q ha hb
    | true =>
      simp only [d7989, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7990 q = 1) (hb : d53227 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7990, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7991 q = 1) (hb : d53228 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7991, d53228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7991, d53228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7992 q = 1) (hb : d53229 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7992, d53229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7992, d53229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7993 q = 1) (hb : d53230 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7993, d53230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7993, d53230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7994 q = 1) (hb : d53231 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7994, d53231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7994, d53231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17923 (p : Pattern) (ha : d7998 p = 1) (hb : d53239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7989 q = 1) (hb : d53226 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11829 q ha hb
    | true =>
      simp only [d7989, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7990 q = 1) (hb : d53227 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7990, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro227 q ha hb
    | true =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7995 q = 1) (hb : d53236 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7995, d53236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7995, d53236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7996 q = 1) (hb : d53237 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7996, d53237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7996, d53237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7997 q = 1) (hb : d53238 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7997, d53238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7997, d53238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7998 q = 1) (hb : d53239 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7998, d53239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7998, d53239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17924 (p : Pattern) (ha : d74424 p = 1) (hb : d85616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7999 q = 1) (hb : d53240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7999, d53240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17922 q ha hb
    | true =>
      simp only [d7999, d53240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17923 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53246 q = 1) (hb : d85612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53246, d85612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53246, d85612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8014 q = 1) (hb : d74419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8014, d74419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11832 q ha hb
    | true =>
      simp only [d8014, d74419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8015 q = 1) (hb : d74420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8015, d74420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8015, d74420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74421 q = 1) (hb : d85613 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74421, d85613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74421, d85613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74422 q = 1) (hb : d85614 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74422, d85614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74422, d85614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74423 q = 1) (hb : d85615 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74423, d85615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74423, d85615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74424 q = 1) (hb : d85616 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74424, d85616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74424, d85616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17925 (p : Pattern) (ha : d74430 p = 1) (hb : d85622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7895 q = 1) (hb : d53071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7895, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7895, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17909 q ha hb
  have h2 (q : Pattern) (ha : d7896 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7896, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7896, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7904 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17909 q ha hb
    | true =>
      simp only [d7904, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17911 q ha hb
  have h4 (q : Pattern) (ha : d7905 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7905, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7906 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7906, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7906, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74388 q = 1) (hb : d85600 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74388, d85600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17916 q ha hb
    | true =>
      simp only [d74388, d85600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17920 q ha hb
  have h7 (q : Pattern) (ha : d7971 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7971, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17912 q ha hb
    | true =>
      simp only [d7971, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro223 q ha hb
  have h8 (q : Pattern) (ha : d74389 q = 1) (hb : d85601 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74389, d85601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74389, d85601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d74390 q = 1) (hb : d85602 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74390, d85602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74390, d85602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74391 q = 1) (hb : d85603 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74391, d85603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74391, d85603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74395 q = 1) (hb : d85607 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74395, d85607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74395, d85607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17921 q ha hb
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
  have h13 (q : Pattern) (ha : d74396 q = 1) (hb : d85608 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74396, d85608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74396, d85608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74397 q = 1) (hb : d85609 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74397, d85609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74397, d85609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74398 q = 1) (hb : d85610 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74398, d85610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74398, d85610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74399 q = 1) (hb : d85611 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74399, d85611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74399, d85611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74425 q = 1) (hb : d85617 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74425, d85617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74425, d85617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17924 q ha hb
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
  have h19 (q : Pattern) (ha : d74426 q = 1) (hb : d85618 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74426, d85618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74426, d85618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d74427 q = 1) (hb : d85619 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74427, d85619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74427, d85619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74428 q = 1) (hb : d85620 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74428, d85620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74428, d85620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74429 q = 1) (hb : d85621 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74429, d85621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74429, d85621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74430 q = 1) (hb : d85622 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74430, d85622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74430, d85622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17926 (p : Pattern) (ha : d74436 p = 1) (hb : d85628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74431 q = 1) (hb : d85623 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74431, d85623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74431, d85623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17925 q ha hb
  have h2 (q : Pattern) (ha : d74432 q = 1) (hb : d85624 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74432, d85624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74432, d85624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74433 q = 1) (hb : d85625 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74433, d85625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74433, d85625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74434 q = 1) (hb : d85626 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74434, d85626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74434, d85626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74435 q = 1) (hb : d85627 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74435, d85627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74435, d85627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74436 q = 1) (hb : d85628 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74436, d85628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74436, d85628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17927 (p : Pattern) (ha : d8043 p = 1) (hb : d53381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11838 q ha hb
    | true =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8042 q = 1) (hb : d53380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8042, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8043 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8043, d53381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8043, d53381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17928 (p : Pattern) (ha : d8049 p = 1) (hb : d53391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8044 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17927 q ha hb
    | true =>
      simp only [d8044, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d8045 q = 1) (hb : d53387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8046 q = 1) (hb : d53388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8046, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8047 q = 1) (hb : d53389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8048 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8049 q = 1) (hb : d53391 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8049, d53391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8049, d53391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17929 (p : Pattern) (ha : d8052 p = 1) (hb : d53394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11838 q ha hb
    | true =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8042 q = 1) (hb : d53380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8042, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8052 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8052, d53394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8052, d53394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17930 (p : Pattern) (ha : d8058 p = 1) (hb : d53401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8044 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17927 q ha hb
    | true =>
      simp only [d8044, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d8045 q = 1) (hb : d53387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8046 q = 1) (hb : d53388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8046, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8047 q = 1) (hb : d53389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8048 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8053 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17929 q ha hb
    | true =>
      simp only [d8053, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h7 (q : Pattern) (ha : d8054 q = 1) (hb : d53397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d53397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8054, d53397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8055 q = 1) (hb : d53398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d53398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8055, d53398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8056 q = 1) (hb : d53399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d53399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d53399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8057 q = 1) (hb : d53400 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d53400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d53400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8058 q = 1) (hb : d53401 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8058, d53401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8058, d53401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17931 (p : Pattern) (ha : d8125 p = 1) (hb : d53475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8044 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17927 q ha hb
    | true =>
      simp only [d8044, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d8045 q = 1) (hb : d53387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8046 q = 1) (hb : d53388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8046, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8047 q = 1) (hb : d53389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8048 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8125 q = 1) (hb : d53475 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8125, d53475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8125, d53475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17932 (p : Pattern) (ha : d8063 p = 1) (hb : d53406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11838 q ha hb
    | true =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8062 q = 1) (hb : d53405 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8063 q = 1) (hb : d53406 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8063, d53406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8063, d53406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17933 (p : Pattern) (ha : d8070 p = 1) (hb : d53415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11838 q ha hb
    | true =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8068 q = 1) (hb : d53413 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8069 q = 1) (hb : d53414 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8069, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8070 q = 1) (hb : d53415 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8070, d53415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8070, d53415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17934 (p : Pattern) (ha : d8081 p = 1) (hb : d53440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8076 q = 1) (hb : d53435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11848 q ha hb
    | true =>
      simp only [d8076, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8077 q = 1) (hb : d53436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8077, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8038 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11838 q ha hb
    | true =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8039 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8078 q = 1) (hb : d53437 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d53437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8078, d53437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8079 q = 1) (hb : d53438 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d53438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8079, d53438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8080 q = 1) (hb : d53439 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d53439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8080, d53439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8081 q = 1) (hb : d53440 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8081, d53440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8081, d53440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17935 (p : Pattern) (ha : d74471 p = 1) (hb : d85637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8064 q = 1) (hb : d53409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17932 q ha hb
    | true =>
      simp only [d8064, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d8065 q = 1) (hb : d53410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8066 q = 1) (hb : d53411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8066, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8067 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8071 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17933 q ha hb
    | true =>
      simp only [d8071, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d8072 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8073 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8073, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8082 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17934 q ha hb
    | true =>
      simp only [d8082, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17927 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53442 q = 1) (hb : d85633 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53442, d85633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53442, d85633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8097 q = 1) (hb : d74466 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d74466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11845 q ha hb
    | true =>
      simp only [d8097, d74466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8098 q = 1) (hb : d74467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, d74467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8098, d74467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74468 q = 1) (hb : d85634 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74468, d85634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74468, d85634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74469 q = 1) (hb : d85635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74469, d85635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74469, d85635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74470 q = 1) (hb : d85636 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74470, d85636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74470, d85636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74471 q = 1) (hb : d85637 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74471, d85637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74471, d85637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17936 (p : Pattern) (ha : d8103 p = 1) (hb : d53449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11838 q ha hb
    | true =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8062 q = 1) (hb : d53405 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8103 q = 1) (hb : d53449 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8103, d53449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8103, d53449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17937 (p : Pattern) (ha : d8108 p = 1) (hb : d53455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11838 q ha hb
    | true =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8068 q = 1) (hb : d53413 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8069 q = 1) (hb : d53414 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8069, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8108 q = 1) (hb : d53455 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8108, d53455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8108, d53455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17938 (p : Pattern) (ha : d8112 p = 1) (hb : d53460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8076 q = 1) (hb : d53435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11848 q ha hb
    | true =>
      simp only [d8076, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8077 q = 1) (hb : d53436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8077, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8038 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11838 q ha hb
    | true =>
      simp only [d8038, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8039 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8078 q = 1) (hb : d53437 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d53437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8078, d53437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8079 q = 1) (hb : d53438 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d53438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8079, d53438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8080 q = 1) (hb : d53439 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d53439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8080, d53439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8112 q = 1) (hb : d53460 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8112, d53460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8112, d53460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17939 (p : Pattern) (ha : d74478 p = 1) (hb : d85642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8064 q = 1) (hb : d53409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17932 q ha hb
    | true =>
      simp only [d8064, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d8065 q = 1) (hb : d53410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8066 q = 1) (hb : d53411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8066, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8067 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8071 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17933 q ha hb
    | true =>
      simp only [d8071, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d8072 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8073 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8073, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8082 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17934 q ha hb
    | true =>
      simp only [d8082, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17927 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53442 q = 1) (hb : d85633 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53442, d85633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53442, d85633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8097 q = 1) (hb : d74466 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d74466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11845 q ha hb
    | true =>
      simp only [d8097, d74466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8098 q = 1) (hb : d74467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, d74467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8098, d74467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74468 q = 1) (hb : d85634 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74468, d85634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74468, d85634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74469 q = 1) (hb : d85635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74469, d85635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74469, d85635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74470 q = 1) (hb : d85636 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74470, d85636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74470, d85636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8104 q = 1) (hb : d53451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8104, d53451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17936 q ha hb
    | true =>
      simp only [d8104, d53451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro308 q ha hb
  have h17 (q : Pattern) (ha : d8105 q = 1) (hb : d53452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8105, d53452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8105, d53452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8106 q = 1) (hb : d53453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8106, d53453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d8106, d53453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d8107 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8107, d53454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8107, d53454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8109 q = 1) (hb : d53457 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8109, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17937 q ha hb
    | true =>
      simp only [d8109, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro310 q ha hb
  have h21 (q : Pattern) (ha : d8110 q = 1) (hb : d53458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8110, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8110, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d8111 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8111, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d8111, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d8113 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17938 q ha hb
    | true =>
      simp only [d8113, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17929 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d53462 q = 1) (hb : d85638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53462, d85638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d53462, d85638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8118 q = 1) (hb : d74473 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d74473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11851 q ha hb
    | true =>
      simp only [d8118, d74473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d8119 q = 1) (hb : d74474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, d74474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d8119, d74474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74475 q = 1) (hb : d85639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74475, d85639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74475, d85639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74476 q = 1) (hb : d85640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74476, d85640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d74476, d85640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74477 q = 1) (hb : d85641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74477, d85641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d74477, d85641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74478 q = 1) (hb : d85642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74478, d85642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74478, d85642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17940 (p : Pattern) (ha : d74485 p = 1) (hb : d85649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8113 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17938 q ha hb
    | true =>
      simp only [d8113, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17929 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53462 q = 1) (hb : d85638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53462, d85638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53462, d85638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8118 q = 1) (hb : d74473 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d74473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11851 q ha hb
    | true =>
      simp only [d8118, d74473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8119 q = 1) (hb : d74474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, d74474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8119, d74474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74475 q = 1) (hb : d85639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74475, d85639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74475, d85639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74483 q = 1) (hb : d85647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74483, d85647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74483, d85647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74484 q = 1) (hb : d85648 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74484, d85648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74484, d85648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74485 q = 1) (hb : d85649 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74485, d85649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74485, d85649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17941 (p : Pattern) (ha : d8149 p = 1) (hb : d53548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8140 q = 1) (hb : d53538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8140, d53538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11861 q ha hb
    | true =>
      simp only [d8140, d53538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8141 q = 1) (hb : d53539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8141, d53539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8141, d53539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8144 q = 1) (hb : d53543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11857 q ha hb
    | true =>
      simp only [d8144, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8145 q = 1) (hb : d53544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8145, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8146 q = 1) (hb : d53545 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8146, d53545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8146, d53545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8147 q = 1) (hb : d53546 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8147, d53546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8147, d53546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8148 q = 1) (hb : d53547 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8148, d53547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8148, d53547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8149 q = 1) (hb : d53548 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8149, d53548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8149, d53548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17942 (p : Pattern) (ha : d8153 p = 1) (hb : d53556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8144 q = 1) (hb : d53543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11857 q ha hb
    | true =>
      simp only [d8144, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8145 q = 1) (hb : d53544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8145, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro286 q ha hb
    | true =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8150 q = 1) (hb : d53553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8150, d53553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8150, d53553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8151 q = 1) (hb : d53554 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8151, d53554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8151, d53554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8152 q = 1) (hb : d53555 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8152, d53555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8152, d53555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8153 q = 1) (hb : d53556 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8153, d53556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8153, d53556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17943 (p : Pattern) (ha : d74515 p = 1) (hb : d85659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8154 q = 1) (hb : d53557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8154, d53557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17941 q ha hb
    | true =>
      simp only [d8154, d53557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17942 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53562 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53563 q = 1) (hb : d85655 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53563, d85655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53563, d85655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8169 q = 1) (hb : d74510 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8169, d74510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11860 q ha hb
    | true =>
      simp only [d8169, d74510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8170 q = 1) (hb : d74511 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8170, d74511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8170, d74511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74512 q = 1) (hb : d85656 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74512, d85656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74512, d85656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74513 q = 1) (hb : d85657 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74513, d85657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74513, d85657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74514 q = 1) (hb : d85658 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74514, d85658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74514, d85658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74515 q = 1) (hb : d85659 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74515, d85659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74515, d85659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17944 (p : Pattern) (ha : d74521 p = 1) (hb : d85665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8050 q = 1) (hb : d53392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8050, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8050, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17928 q ha hb
  have h2 (q : Pattern) (ha : d8051 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8051, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8051, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8059 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17928 q ha hb
    | true =>
      simp only [d8059, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17930 q ha hb
  have h4 (q : Pattern) (ha : d8060 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8060, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8061 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8061, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8061, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74479 q = 1) (hb : d85643 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74479, d85643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17935 q ha hb
    | true =>
      simp only [d74479, d85643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17939 q ha hb
  have h7 (q : Pattern) (ha : d8126 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8126, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17931 q ha hb
    | true =>
      simp only [d8126, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q ha hb
  have h8 (q : Pattern) (ha : d74480 q = 1) (hb : d85644 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74480, d85644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74480, d85644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d74481 q = 1) (hb : d85645 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74481, d85645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74481, d85645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74482 q = 1) (hb : d85646 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74482, d85646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74482, d85646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74486 q = 1) (hb : d85650 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74486, d85650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74486, d85650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17940 q ha hb
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
  have h13 (q : Pattern) (ha : d74487 q = 1) (hb : d85651 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74487, d85651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74487, d85651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74488 q = 1) (hb : d85652 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74488, d85652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74488, d85652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74489 q = 1) (hb : d85653 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74489, d85653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74489, d85653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74490 q = 1) (hb : d85654 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74490, d85654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74490, d85654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74516 q = 1) (hb : d85660 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74516, d85660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74516, d85660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17943 q ha hb
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
  have h19 (q : Pattern) (ha : d74517 q = 1) (hb : d85661 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74517, d85661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74517, d85661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d74518 q = 1) (hb : d85662 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74518, d85662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74518, d85662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74519 q = 1) (hb : d85663 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74519, d85663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74519, d85663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74520 q = 1) (hb : d85664 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74520, d85664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74520, d85664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74521 q = 1) (hb : d85665 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74521, d85665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74521, d85665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17945 (p : Pattern) (ha : d74527 p = 1) (hb : d85671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74522 q = 1) (hb : d85666 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74522, d85666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74522, d85666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17944 q ha hb
  have h2 (q : Pattern) (ha : d74523 q = 1) (hb : d85667 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74523, d85667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74523, d85667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74524 q = 1) (hb : d85668 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74524, d85668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74524, d85668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74525 q = 1) (hb : d85669 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74525, d85669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74525, d85669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74526 q = 1) (hb : d85670 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74526, d85670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74526, d85670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74527 q = 1) (hb : d85671 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74527, d85671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74527, d85671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17946 (p : Pattern) (ha : d74533 p = 1) (hb : d85677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d74173 q = 1) (hb : d85506 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74173, d85506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17850 q ha hb
    | true =>
      simp only [d74173, d85506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17869 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74258 q = 1) (hb : d85546 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74258, d85546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74258, d85546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17888 q ha hb
  have h3 (q : Pattern) (ha : d74259 q = 1) (hb : d85547 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74259, d85547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74259, d85547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74347 q = 1) (hb : d85587 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74347, d85587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74347, d85587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17907 q ha hb
  have h5 (q : Pattern) (ha : d74348 q = 1) (hb : d85588 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74348, d85588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74348, d85588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74349 q = 1) (hb : d85589 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74349, d85589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74349, d85589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74437 q = 1) (hb : d85629 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74437, d85629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74437, d85629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17926 q ha hb
  have h8 (q : Pattern) (ha : d74438 q = 1) (hb : d85630 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74438, d85630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74438, d85630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74439 q = 1) (hb : d85631 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74439, d85631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74439, d85631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74440 q = 1) (hb : d85632 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74440, d85632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74440, d85632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74528 q = 1) (hb : d85672 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74528, d85672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74528, d85672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17945 q ha hb
  have h12 (q : Pattern) (ha : d74529 q = 1) (hb : d85673 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74529, d85673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74529, d85673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74530 q = 1) (hb : d85674 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74530, d85674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74530, d85674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74531 q = 1) (hb : d85675 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74531, d85675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74531, d85675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74532 q = 1) (hb : d85676 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74532, d85676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74532, d85676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74533 q = 1) (hb : d85677 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74533, d85677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74533, d85677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro17947 (p : Pattern) (ha : d74539 p = 1) (hb : d85683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74534 q = 1) (hb : d85678 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74534, d85678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17946 q ha hb
    | true =>
      simp only [d74534, d85678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74535 q = 1) (hb : d85679 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74535, d85679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74535, d85679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74536 q = 1) (hb : d85680 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74536, d85680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74536, d85680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74537 q = 1) (hb : d85681 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74537, d85681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74537, d85681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74538 q = 1) (hb : d85682 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74538, d85682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74538, d85682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74539 q = 1) (hb : d85683 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74539, d85683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74539, d85683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17948 (p : Pattern) (ha : d74545 p = 1) (hb : d85689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74540 q = 1) (hb : d85684 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74540, d85684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17947 q ha hb
    | true =>
      simp only [d74540, d85684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74541 q = 1) (hb : d85685 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74541, d85685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74541, d85685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74542 q = 1) (hb : d85686 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74542, d85686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74542, d85686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74543 q = 1) (hb : d85687 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74543, d85687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74543, d85687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74544 q = 1) (hb : d85688 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74544, d85688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74544, d85688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74545 q = 1) (hb : d85689 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74545, d85689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74545, d85689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17949 (p : Pattern) (ha : d74551 p = 1) (hb : d85695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74546 q = 1) (hb : d85690 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74546, d85690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17948 q ha hb
    | true =>
      simp only [d74546, d85690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74547 q = 1) (hb : d85691 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74547, d85691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74547, d85691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74548 q = 1) (hb : d85692 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74548, d85692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74548, d85692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74549 q = 1) (hb : d85693 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74549, d85693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74549, d85693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74550 q = 1) (hb : d85694 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74550, d85694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74550, d85694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74551 q = 1) (hb : d85695 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74551, d85695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74551, d85695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17950 (p : Pattern) (ha : d74557 p = 1) (hb : d85701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74552 q = 1) (hb : d85696 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74552, d85696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17949 q ha hb
    | true =>
      simp only [d74552, d85696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74553 q = 1) (hb : d85697 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74553, d85697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74553, d85697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74554 q = 1) (hb : d85698 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74554, d85698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74554, d85698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74555 q = 1) (hb : d85699 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74555, d85699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74555, d85699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74556 q = 1) (hb : d85700 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74556, d85700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74556, d85700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74557 q = 1) (hb : d85701 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74557, d85701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74557, d85701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17951 (p : Pattern) (ha : d74563 p = 1) (hb : d85707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74558 q = 1) (hb : d85702 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74558, d85702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17950 q ha hb
    | true =>
      simp only [d74558, d85702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74559 q = 1) (hb : d85703 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74559, d85703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74559, d85703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74560 q = 1) (hb : d85704 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74560, d85704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74560, d85704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74561 q = 1) (hb : d85705 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74561, d85705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74561, d85705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74562 q = 1) (hb : d85706 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74562, d85706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74562, d85706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74563 q = 1) (hb : d85707 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74563, d85707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74563, d85707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17952 (p : Pattern) (ha : d74569 p = 1) (hb : d85713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74564 q = 1) (hb : d85708 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74564, d85708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17951 q ha hb
    | true =>
      simp only [d74564, d85708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74565 q = 1) (hb : d85709 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74565, d85709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74565, d85709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74566 q = 1) (hb : d85710 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74566, d85710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74566, d85710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74567 q = 1) (hb : d85711 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74567, d85711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74567, d85711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74568 q = 1) (hb : d85712 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74568, d85712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74568, d85712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74569 q = 1) (hb : d85713 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74569, d85713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74569, d85713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17953 (p : Pattern) (ha : d74575 p = 1) (hb : d85719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74570 q = 1) (hb : d85714 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74570, d85714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17952 q ha hb
    | true =>
      simp only [d74570, d85714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74571 q = 1) (hb : d85715 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74571, d85715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74571, d85715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74572 q = 1) (hb : d85716 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74572, d85716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74572, d85716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74573 q = 1) (hb : d85717 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74573, d85717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74573, d85717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74574 q = 1) (hb : d85718 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74574, d85718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74574, d85718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74575 q = 1) (hb : d85719 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74575, d85719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74575, d85719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17954 (p : Pattern) (ha : d99409 p = 1) (hb : d104542 p = 1) : d99409 p = 1 := by
  have h0 (q : Pattern) (ha : d99409 q = 1) (hb : d104542 q = 1) : d99409 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro17955 (p : Pattern) (ha : d7302 p = 1) (hb : d74080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7248 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17827 q ha hb
    | true =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d7298 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7298, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7299 q = 1) (hb : d74077 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d74077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7299, d74077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7300 q = 1) (hb : d74078 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d74078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7300, d74078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7301 q = 1) (hb : d74079 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d74079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7301, d74079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7302 q = 1) (hb : d74080 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7302, d74080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7302, d74080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17956 (p : Pattern) (ha : d7309 p = 1) (hb : d74087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7248 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17827 q ha hb
    | true =>
      simp only [d7248, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d7298 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7298, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7299 q = 1) (hb : d74077 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d74077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7299, d74077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7300 q = 1) (hb : d74078 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d74078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7300, d74078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7301 q = 1) (hb : d74079 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d74079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d74079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7255 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17829 q ha hb
    | true =>
      simp only [d7255, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d7305 q = 1) (hb : d52155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7305, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7306 q = 1) (hb : d74084 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d74084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7306, d74084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7307 q = 1) (hb : d74085 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d74085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7307, d74085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7308 q = 1) (hb : d74086 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d74086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7308, d74086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7309 q = 1) (hb : d74087 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7309, d74087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7309, d74087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17957 (p : Pattern) (ha : d74094 p = 1) (hb : d99199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7255 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17829 q ha hb
    | true =>
      simp only [d7255, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d7305 q = 1) (hb : d52155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7305, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7306 q = 1) (hb : d74084 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d74084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7306, d74084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7307 q = 1) (hb : d74092 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d74092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d74092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7308 q = 1) (hb : d74093 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d74093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d74093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74094 q = 1) (hb : d99199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74094, d99199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74094, d99199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro17958 (p : Pattern) (ha : d74109 p = 1) (hb : d99209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52196 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7281 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17832 q ha hb
    | true =>
      simp only [d7281, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d52197 q = 1) (hb : d99205 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52197, d99205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52197, d99205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74106 q = 1) (hb : d99206 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74106, d99206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74106, d99206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74107 q = 1) (hb : d99207 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74107, d99207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74107, d99207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74108 q = 1) (hb : d99208 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74108, d99208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74108, d99208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74109 q = 1) (hb : d99209 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74109, d99209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74109, d99209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17959 (p : Pattern) (ha : d74115 p = 1) (hb : d99215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7310 q = 1) (hb : d74088 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d74088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17955 q ha hb
    | true =>
      simp only [d7310, d74088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17956 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7311 q = 1) (hb : d74089 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d74089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7311, d74089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74090 q = 1) (hb : d99197 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74090, d99197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74090, d99197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74091 q = 1) (hb : d99198 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74091, d99198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74091, d99198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74095 q = 1) (hb : d99200 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74095, d99200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74095, d99200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17957 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74096 q = 1) (hb : d99201 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74096, d99201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74096, d99201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74097 q = 1) (hb : d99202 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74097, d99202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74097, d99202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74098 q = 1) (hb : d99203 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74098, d99203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74098, d99203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74099 q = 1) (hb : d99204 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74099, d99204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74099, d99204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74110 q = 1) (hb : d99210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74110, d99210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74110, d99210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17958 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74111 q = 1) (hb : d99211 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74111, d99211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74111, d99211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74112 q = 1) (hb : d99212 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74112, d99212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74112, d99212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74113 q = 1) (hb : d99213 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74113, d99213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74113, d99213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74114 q = 1) (hb : d99214 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74114, d99214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74114, d99214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74115 q = 1) (hb : d99215 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74115, d99215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74115, d99215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17960 (p : Pattern) (ha : d74121 p = 1) (hb : d99221 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d74116 q = 1) (hb : d99216 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74116, d99216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74116, d99216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17959 q ha hb
  have h8 (q : Pattern) (ha : d74117 q = 1) (hb : d99217 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74117, d99217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74117, d99217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74118 q = 1) (hb : d99218 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74118, d99218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74118, d99218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74119 q = 1) (hb : d99219 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74119, d99219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74119, d99219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74120 q = 1) (hb : d99220 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74120, d99220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74120, d99220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74121 q = 1) (hb : d99221 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74121, d99221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74121, d99221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro17961 (p : Pattern) (ha : d7439 p = 1) (hb : d74131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7434 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17851 q ha hb
    | true =>
      simp only [d7434, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h5 (q : Pattern) (ha : d7435 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7435, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7436 q = 1) (hb : d74128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d74128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7436, d74128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7437 q = 1) (hb : d74129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d74129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7437, d74129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7438 q = 1) (hb : d74130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d74130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7438, d74130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7439 q = 1) (hb : d74131 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7439, d74131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7439, d74131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17962 (p : Pattern) (ha : d7448 p = 1) (hb : d74138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7434 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17851 q ha hb
    | true =>
      simp only [d7434, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h4 (q : Pattern) (ha : d7435 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7435, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7436 q = 1) (hb : d74128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d74128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7436, d74128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7437 q = 1) (hb : d74129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d74129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7437, d74129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7438 q = 1) (hb : d74130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d74130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d74130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7443 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17853 q ha hb
    | true =>
      simp only [d7443, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h13 (q : Pattern) (ha : d7444 q = 1) (hb : d52329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7444, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7445 q = 1) (hb : d74135 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d74135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7445, d74135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7446 q = 1) (hb : d74136 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d74136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7446, d74136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7447 q = 1) (hb : d74137 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d74137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7447, d74137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7448 q = 1) (hb : d74138 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7448, d74138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7448, d74138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17963 (p : Pattern) (ha : d74145 p = 1) (hb : d99224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7443 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17853 q ha hb
    | true =>
      simp only [d7443, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h3 (q : Pattern) (ha : d7444 q = 1) (hb : d52329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7444, d52329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7445 q = 1) (hb : d74135 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d74135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7445, d74135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7446 q = 1) (hb : d74143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d74143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d74143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7447 q = 1) (hb : d74144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d74144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d74144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74145 q = 1) (hb : d99224 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74145, d99224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74145, d99224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro17964 (p : Pattern) (ha : d74160 p = 1) (hb : d99235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52399 q = 1) (hb : d99230 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52399, d99230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17866 q hb ha
    | true =>
      simp only [d52399, d99230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72 q hb ha
  have h3 (q : Pattern) (ha : d52400 q = 1) (hb : d99231 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52400, d99231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52400, d99231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74156 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74157 q = 1) (hb : d99232 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74157, d99232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74157, d99232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74158 q = 1) (hb : d99233 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74158, d99233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74158, d99233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74159 q = 1) (hb : d99234 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74159, d99234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74159, d99234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74160 q = 1) (hb : d99235 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74160, d99235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74160, d99235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17965 (p : Pattern) (ha : d74166 p = 1) (hb : d99241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7449 q = 1) (hb : d74139 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d74139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17961 q ha hb
    | true =>
      simp only [d7449, d74139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17962 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7450 q = 1) (hb : d74140 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d74140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7450, d74140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74141 q = 1) (hb : d99222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74141, d99222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74141, d99222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74142 q = 1) (hb : d99223 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74142, d99223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74142, d99223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74146 q = 1) (hb : d99225 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74146, d99225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74146, d99225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17963 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74147 q = 1) (hb : d99226 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74147, d99226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74147, d99226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74148 q = 1) (hb : d99227 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74148, d99227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74148, d99227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74149 q = 1) (hb : d99228 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74149, d99228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74149, d99228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74150 q = 1) (hb : d99229 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74150, d99229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74150, d99229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74161 q = 1) (hb : d99236 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74161, d99236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74161, d99236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17964 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74162 q = 1) (hb : d99237 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74162, d99237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74162, d99237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74163 q = 1) (hb : d99238 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74163, d99238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74163, d99238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74164 q = 1) (hb : d99239 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74164, d99239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74164, d99239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74165 q = 1) (hb : d99240 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74165, d99240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74165, d99240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74166 q = 1) (hb : d99241 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74166, d99241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74166, d99241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17966 (p : Pattern) (ha : d74172 p = 1) (hb : d99247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74167 q = 1) (hb : d99242 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74167, d99242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74167, d99242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17965 q ha hb
  have h2 (q : Pattern) (ha : d74168 q = 1) (hb : d99243 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74168, d99243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74168, d99243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74169 q = 1) (hb : d99244 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74169, d99244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74169, d99244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74170 q = 1) (hb : d99245 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74170, d99245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74170, d99245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74171 q = 1) (hb : d99246 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74171, d99246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74171, d99246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74172 q = 1) (hb : d99247 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74172, d99247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74172, d99247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17967 (p : Pattern) (ha : d7587 p = 1) (hb : d74201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7582 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17870 q ha hb
    | true =>
      simp only [d7582, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h5 (q : Pattern) (ha : d7583 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7583, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74197 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7584 q = 1) (hb : d74198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d74198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7584, d74198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7585 q = 1) (hb : d74199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d74199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7585, d74199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7586 q = 1) (hb : d74200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d74200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7586, d74200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7587 q = 1) (hb : d74201 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7587, d74201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7587, d74201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17968 (p : Pattern) (ha : d7596 p = 1) (hb : d74208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7582 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17870 q ha hb
    | true =>
      simp only [d7582, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h4 (q : Pattern) (ha : d7583 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7583, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74197 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7584 q = 1) (hb : d74198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d74198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7584, d74198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7585 q = 1) (hb : d74199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d74199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7585, d74199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7586 q = 1) (hb : d74200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d74200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d74200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7591 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17872 q ha hb
    | true =>
      simp only [d7591, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h13 (q : Pattern) (ha : d7592 q = 1) (hb : d52550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7592, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74204 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7593 q = 1) (hb : d74205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d74205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7593, d74205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7594 q = 1) (hb : d74206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d74206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7594, d74206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7595 q = 1) (hb : d74207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d74207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7595, d74207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7596 q = 1) (hb : d74208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7596, d74208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7596, d74208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17969 (p : Pattern) (ha : d74215 p = 1) (hb : d99251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7591 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17872 q ha hb
    | true =>
      simp only [d7591, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h3 (q : Pattern) (ha : d7592 q = 1) (hb : d52550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7592, d52550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74204 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7593 q = 1) (hb : d74205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d74205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7593, d74205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7594 q = 1) (hb : d74213 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d74213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d74213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7595 q = 1) (hb : d74214 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d74214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d74214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74215 q = 1) (hb : d99251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74215, d99251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74215, d99251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro17970 (p : Pattern) (ha : d74245 p = 1) (hb : d99262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52631 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52636 q = 1) (hb : d99257 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52636, d99257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17885 q hb ha
    | true =>
      simp only [d52636, d99257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro118 q hb ha
  have h3 (q : Pattern) (ha : d52637 q = 1) (hb : d99258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52637, d99258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52637, d99258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74241 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74242 q = 1) (hb : d99259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74242, d99259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74242, d99259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74243 q = 1) (hb : d99260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74243, d99260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74243, d99260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74244 q = 1) (hb : d99261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74244, d99261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74244, d99261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74245 q = 1) (hb : d99262 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74245, d99262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74245, d99262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17971 (p : Pattern) (ha : d74251 p = 1) (hb : d99268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7597 q = 1) (hb : d74209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d74209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17967 q ha hb
    | true =>
      simp only [d7597, d74209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17968 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7598 q = 1) (hb : d74210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d74210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7598, d74210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74211 q = 1) (hb : d99249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74211, d99249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74211, d99249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74212 q = 1) (hb : d99250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74212, d99250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74212, d99250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74216 q = 1) (hb : d99252 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74216, d99252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74216, d99252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17969 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74217 q = 1) (hb : d99253 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74217, d99253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74217, d99253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74218 q = 1) (hb : d99254 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74218, d99254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74218, d99254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74219 q = 1) (hb : d99255 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74219, d99255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74219, d99255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74220 q = 1) (hb : d99256 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74220, d99256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74220, d99256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74246 q = 1) (hb : d99263 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74246, d99263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74246, d99263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17970 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74247 q = 1) (hb : d99264 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74247, d99264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74247, d99264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74248 q = 1) (hb : d99265 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74248, d99265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74248, d99265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74249 q = 1) (hb : d99266 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74249, d99266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74249, d99266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74250 q = 1) (hb : d99267 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74250, d99267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74250, d99267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74251 q = 1) (hb : d99268 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74251, d99268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74251, d99268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17972 (p : Pattern) (ha : d74257 p = 1) (hb : d99274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74252 q = 1) (hb : d99269 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74252, d99269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74252, d99269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17971 q ha hb
  have h2 (q : Pattern) (ha : d74253 q = 1) (hb : d99270 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74253, d99270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74253, d99270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74254 q = 1) (hb : d99271 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74254, d99271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74254, d99271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74255 q = 1) (hb : d99272 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74255, d99272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74255, d99272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74256 q = 1) (hb : d99273 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74256, d99273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74256, d99273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74257 q = 1) (hb : d99274 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74257, d99274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74257, d99274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17973 (p : Pattern) (ha : d7740 p = 1) (hb : d74290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7735 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17889 q ha hb
    | true =>
      simp only [d7735, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h5 (q : Pattern) (ha : d7736 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7736, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74286 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7737 q = 1) (hb : d74287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d74287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7737, d74287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7738 q = 1) (hb : d74288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d74288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7738, d74288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7739 q = 1) (hb : d74289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d74289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7739, d74289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7740 q = 1) (hb : d74290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7740, d74290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7740, d74290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17974 (p : Pattern) (ha : d7749 p = 1) (hb : d74297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7735 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17889 q ha hb
    | true =>
      simp only [d7735, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h4 (q : Pattern) (ha : d7736 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7736, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74286 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7737 q = 1) (hb : d74287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d74287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7737, d74287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7738 q = 1) (hb : d74288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d74288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7738, d74288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7739 q = 1) (hb : d74289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d74289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d74289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7744 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17891 q ha hb
    | true =>
      simp only [d7744, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h13 (q : Pattern) (ha : d7745 q = 1) (hb : d52830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7745, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74293 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7746 q = 1) (hb : d74294 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d74294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7746, d74294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7747 q = 1) (hb : d74295 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d74295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7747, d74295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7748 q = 1) (hb : d74296 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d74296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7748, d74296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7749 q = 1) (hb : d74297 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7749, d74297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7749, d74297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17975 (p : Pattern) (ha : d74304 p = 1) (hb : d99279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7744 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17891 q ha hb
    | true =>
      simp only [d7744, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h3 (q : Pattern) (ha : d7745 q = 1) (hb : d52830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7745, d52830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74293 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7746 q = 1) (hb : d74294 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d74294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7746, d74294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7747 q = 1) (hb : d74302 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d74302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d74302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7748 q = 1) (hb : d74303 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d74303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d74303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74304 q = 1) (hb : d99279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74304, d99279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74304, d99279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro17976 (p : Pattern) (ha : d74334 p = 1) (hb : d99290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52930 q = 1) (hb : d99285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52930, d99285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17904 q hb ha
    | true =>
      simp only [d52930, d99285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro170 q hb ha
  have h3 (q : Pattern) (ha : d52931 q = 1) (hb : d99286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52931, d99286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52931, d99286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74330 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74331 q = 1) (hb : d99287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74331, d99287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74331, d99287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74332 q = 1) (hb : d99288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74332, d99288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74332, d99288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74333 q = 1) (hb : d99289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74333, d99289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74333, d99289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74334 q = 1) (hb : d99290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74334, d99290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74334, d99290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17977 (p : Pattern) (ha : d74340 p = 1) (hb : d99296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7750 q = 1) (hb : d74298 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d74298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17973 q ha hb
    | true =>
      simp only [d7750, d74298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17974 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7751 q = 1) (hb : d74299 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d74299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7751, d74299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74300 q = 1) (hb : d99277 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74300, d99277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74300, d99277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74301 q = 1) (hb : d99278 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74301, d99278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74301, d99278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74305 q = 1) (hb : d99280 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74305, d99280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74305, d99280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17975 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74306 q = 1) (hb : d99281 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74306, d99281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74306, d99281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74307 q = 1) (hb : d99282 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74307, d99282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74307, d99282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74308 q = 1) (hb : d99283 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74308, d99283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74308, d99283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74309 q = 1) (hb : d99284 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74309, d99284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74309, d99284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74335 q = 1) (hb : d99291 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74335, d99291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74335, d99291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17976 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74336 q = 1) (hb : d99292 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74336, d99292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74336, d99292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74337 q = 1) (hb : d99293 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74337, d99293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74337, d99293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74338 q = 1) (hb : d99294 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74338, d99294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74338, d99294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74339 q = 1) (hb : d99295 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74339, d99295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74339, d99295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74340 q = 1) (hb : d99296 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74340, d99296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74340, d99296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17978 (p : Pattern) (ha : d74346 p = 1) (hb : d99302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74341 q = 1) (hb : d99297 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74341, d99297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74341, d99297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17977 q ha hb
  have h2 (q : Pattern) (ha : d74342 q = 1) (hb : d99298 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74342, d99298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74342, d99298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74343 q = 1) (hb : d99299 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74343, d99299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74343, d99299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74344 q = 1) (hb : d99300 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74344, d99300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74344, d99300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74345 q = 1) (hb : d99301 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74345, d99301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74345, d99301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74346 q = 1) (hb : d99302 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74346, d99302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74346, d99302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17979 (p : Pattern) (ha : d7894 p = 1) (hb : d74380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7889 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17908 q ha hb
    | true =>
      simp only [d7889, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h5 (q : Pattern) (ha : d7890 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7890, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74376 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7891 q = 1) (hb : d74377 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d74377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7891, d74377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7892 q = 1) (hb : d74378 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d74378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7892, d74378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7893 q = 1) (hb : d74379 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d74379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7893, d74379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7894 q = 1) (hb : d74380 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7894, d74380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7894, d74380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17980 (p : Pattern) (ha : d7903 p = 1) (hb : d74387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7889 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17908 q ha hb
    | true =>
      simp only [d7889, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h4 (q : Pattern) (ha : d7890 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7890, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74376 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7891 q = 1) (hb : d74377 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d74377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7891, d74377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7892 q = 1) (hb : d74378 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d74378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7892, d74378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7893 q = 1) (hb : d74379 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d74379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d74379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7898 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17910 q ha hb
    | true =>
      simp only [d7898, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h13 (q : Pattern) (ha : d7899 q = 1) (hb : d53145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7899, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74383 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7900 q = 1) (hb : d74384 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d74384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7900, d74384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7901 q = 1) (hb : d74385 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d74385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7901, d74385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7902 q = 1) (hb : d74386 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d74386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7902, d74386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7903 q = 1) (hb : d74387 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7903, d74387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7903, d74387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17981 (p : Pattern) (ha : d74394 p = 1) (hb : d99308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7898 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17910 q ha hb
    | true =>
      simp only [d7898, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h3 (q : Pattern) (ha : d7899 q = 1) (hb : d53145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7899, d53145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74383 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7900 q = 1) (hb : d74384 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d74384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7900, d74384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7901 q = 1) (hb : d74392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d74392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d74392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7902 q = 1) (hb : d74393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d74393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d74393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74394 q = 1) (hb : d99308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74394, d99308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74394, d99308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro17982 (p : Pattern) (ha : d74424 p = 1) (hb : d99319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53240 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53245 q = 1) (hb : d99314 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53245, d99314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17923 q hb ha
    | true =>
      simp only [d53245, d99314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro228 q hb ha
  have h3 (q : Pattern) (ha : d53246 q = 1) (hb : d99315 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53246, d99315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53246, d99315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74420 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74421 q = 1) (hb : d99316 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74421, d99316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74421, d99316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74422 q = 1) (hb : d99317 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74422, d99317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74422, d99317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74423 q = 1) (hb : d99318 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74423, d99318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74423, d99318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74424 q = 1) (hb : d99319 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74424, d99319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74424, d99319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17983 (p : Pattern) (ha : d74430 p = 1) (hb : d99325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7904 q = 1) (hb : d74388 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d74388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17979 q ha hb
    | true =>
      simp only [d7904, d74388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17980 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7905 q = 1) (hb : d74389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d74389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7905, d74389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74390 q = 1) (hb : d99306 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74390, d99306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74390, d99306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74391 q = 1) (hb : d99307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74391, d99307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74391, d99307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74395 q = 1) (hb : d99309 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74395, d99309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74395, d99309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17981 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74396 q = 1) (hb : d99310 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74396, d99310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74396, d99310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74397 q = 1) (hb : d99311 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74397, d99311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74397, d99311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74398 q = 1) (hb : d99312 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74398, d99312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74398, d99312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74399 q = 1) (hb : d99313 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74399, d99313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74399, d99313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74425 q = 1) (hb : d99320 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74425, d99320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74425, d99320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17982 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74426 q = 1) (hb : d99321 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74426, d99321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74426, d99321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74427 q = 1) (hb : d99322 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74427, d99322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74427, d99322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74428 q = 1) (hb : d99323 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74428, d99323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74428, d99323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74429 q = 1) (hb : d99324 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74429, d99324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74429, d99324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74430 q = 1) (hb : d99325 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74430, d99325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74430, d99325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17984 (p : Pattern) (ha : d74436 p = 1) (hb : d99331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74431 q = 1) (hb : d99326 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74431, d99326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74431, d99326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17983 q ha hb
  have h2 (q : Pattern) (ha : d74432 q = 1) (hb : d99327 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74432, d99327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74432, d99327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74433 q = 1) (hb : d99328 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74433, d99328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74433, d99328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74434 q = 1) (hb : d99329 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74434, d99329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74434, d99329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74435 q = 1) (hb : d99330 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74435, d99330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74435, d99330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74436 q = 1) (hb : d99331 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74436, d99331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74436, d99331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17985 (p : Pattern) (ha : d8049 p = 1) (hb : d74471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8044 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17927 q ha hb
    | true =>
      simp only [d8044, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h5 (q : Pattern) (ha : d8045 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8045, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74467 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8046 q = 1) (hb : d74468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d74468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8046, d74468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8047 q = 1) (hb : d74469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d74469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8047, d74469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8048 q = 1) (hb : d74470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d74470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8048, d74470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8049 q = 1) (hb : d74471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8049, d74471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8049, d74471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17986 (p : Pattern) (ha : d8058 p = 1) (hb : d74478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8044 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17927 q ha hb
    | true =>
      simp only [d8044, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h4 (q : Pattern) (ha : d8045 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8045, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74467 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8046 q = 1) (hb : d74468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d74468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8046, d74468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8047 q = 1) (hb : d74469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d74469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8047, d74469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8048 q = 1) (hb : d74470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d74470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d74470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8053 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17929 q ha hb
    | true =>
      simp only [d8053, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h13 (q : Pattern) (ha : d8054 q = 1) (hb : d53462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8054, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74474 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8055 q = 1) (hb : d74475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d74475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8055, d74475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8056 q = 1) (hb : d74476 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d74476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8056, d74476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8057 q = 1) (hb : d74477 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d74477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8057, d74477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8058 q = 1) (hb : d74478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8058, d74478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8058, d74478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17987 (p : Pattern) (ha : d74485 p = 1) (hb : d99338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8053 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17929 q ha hb
    | true =>
      simp only [d8053, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h3 (q : Pattern) (ha : d8054 q = 1) (hb : d53462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8054, d53462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74474 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8055 q = 1) (hb : d74475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d74475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8055, d74475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8056 q = 1) (hb : d74483 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d74483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d74483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8057 q = 1) (hb : d74484 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d74484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d74484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74485 q = 1) (hb : d99338 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74485, d99338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74485, d99338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro17988 (p : Pattern) (ha : d74515 p = 1) (hb : d99349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53562 q = 1) (hb : d99344 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53562, d99344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17942 q hb ha
    | true =>
      simp only [d53562, d99344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro287 q hb ha
  have h3 (q : Pattern) (ha : d53563 q = 1) (hb : d99345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53563, d99345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53563, d99345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74511 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74512 q = 1) (hb : d99346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74512, d99346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74512, d99346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74513 q = 1) (hb : d99347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74513, d99347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74513, d99347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74514 q = 1) (hb : d99348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74514, d99348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74514, d99348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74515 q = 1) (hb : d99349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74515, d99349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74515, d99349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17989 (p : Pattern) (ha : d74521 p = 1) (hb : d99355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8059 q = 1) (hb : d74479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d74479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17985 q ha hb
    | true =>
      simp only [d8059, d74479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17986 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8060 q = 1) (hb : d74480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d74480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8060, d74480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74481 q = 1) (hb : d99336 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74481, d99336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74481, d99336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74482 q = 1) (hb : d99337 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74482, d99337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74482, d99337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74486 q = 1) (hb : d99339 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74486, d99339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74486, d99339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17987 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74487 q = 1) (hb : d99340 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74487, d99340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74487, d99340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74488 q = 1) (hb : d99341 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74488, d99341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74488, d99341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74489 q = 1) (hb : d99342 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74489, d99342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74489, d99342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74490 q = 1) (hb : d99343 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74490, d99343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74490, d99343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74516 q = 1) (hb : d99350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74516, d99350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74516, d99350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17988 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74517 q = 1) (hb : d99351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74517, d99351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74517, d99351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74518 q = 1) (hb : d99352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74518, d99352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74518, d99352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74519 q = 1) (hb : d99353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74519, d99353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74519, d99353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74520 q = 1) (hb : d99354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74520, d99354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74520, d99354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74521 q = 1) (hb : d99355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74521, d99355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74521, d99355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17990 (p : Pattern) (ha : d74527 p = 1) (hb : d99361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74522 q = 1) (hb : d99356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74522, d99356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74522, d99356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17989 q ha hb
  have h2 (q : Pattern) (ha : d74523 q = 1) (hb : d99357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74523, d99357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74523, d99357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74524 q = 1) (hb : d99358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74524, d99358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74524, d99358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74525 q = 1) (hb : d99359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74525, d99359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74525, d99359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74526 q = 1) (hb : d99360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74526, d99360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74526, d99360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74527 q = 1) (hb : d99361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74527, d99361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74527, d99361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17991 (p : Pattern) (ha : d74533 p = 1) (hb : d99367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d74173 q = 1) (hb : d99248 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74173, d99248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17960 q ha hb
    | true =>
      simp only [d74173, d99248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17966 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74258 q = 1) (hb : d99275 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74258, d99275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74258, d99275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17972 q ha hb
  have h3 (q : Pattern) (ha : d74259 q = 1) (hb : d99276 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74259, d99276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74259, d99276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74347 q = 1) (hb : d99303 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74347, d99303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74347, d99303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17978 q ha hb
  have h5 (q : Pattern) (ha : d74348 q = 1) (hb : d99304 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74348, d99304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74348, d99304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74349 q = 1) (hb : d99305 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74349, d99305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74349, d99305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74437 q = 1) (hb : d99332 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74437, d99332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74437, d99332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17984 q ha hb
  have h8 (q : Pattern) (ha : d74438 q = 1) (hb : d99333 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74438, d99333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74438, d99333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74439 q = 1) (hb : d99334 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74439, d99334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74439, d99334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74440 q = 1) (hb : d99335 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74440, d99335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74440, d99335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74528 q = 1) (hb : d99362 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74528, d99362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74528, d99362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17990 q ha hb
  have h12 (q : Pattern) (ha : d74529 q = 1) (hb : d99363 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74529, d99363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74529, d99363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74530 q = 1) (hb : d99364 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74530, d99364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74530, d99364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74531 q = 1) (hb : d99365 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74531, d99365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74531, d99365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74532 q = 1) (hb : d99366 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74532, d99366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74532, d99366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74533 q = 1) (hb : d99367 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74533, d99367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74533, d99367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro17992 (p : Pattern) (ha : d74539 p = 1) (hb : d99373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74534 q = 1) (hb : d99368 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74534, d99368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17991 q ha hb
    | true =>
      simp only [d74534, d99368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74535 q = 1) (hb : d99369 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74535, d99369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74535, d99369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74536 q = 1) (hb : d99370 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74536, d99370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74536, d99370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74537 q = 1) (hb : d99371 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74537, d99371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74537, d99371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74538 q = 1) (hb : d99372 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74538, d99372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74538, d99372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74539 q = 1) (hb : d99373 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74539, d99373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74539, d99373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17993 (p : Pattern) (ha : d74545 p = 1) (hb : d99379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74540 q = 1) (hb : d99374 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74540, d99374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17992 q ha hb
    | true =>
      simp only [d74540, d99374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74541 q = 1) (hb : d99375 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74541, d99375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74541, d99375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74542 q = 1) (hb : d99376 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74542, d99376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74542, d99376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74543 q = 1) (hb : d99377 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74543, d99377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74543, d99377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74544 q = 1) (hb : d99378 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74544, d99378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74544, d99378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74545 q = 1) (hb : d99379 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74545, d99379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74545, d99379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17994 (p : Pattern) (ha : d74551 p = 1) (hb : d99385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74546 q = 1) (hb : d99380 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74546, d99380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17993 q ha hb
    | true =>
      simp only [d74546, d99380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74547 q = 1) (hb : d99381 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74547, d99381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74547, d99381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74548 q = 1) (hb : d99382 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74548, d99382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74548, d99382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74549 q = 1) (hb : d99383 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74549, d99383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74549, d99383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74550 q = 1) (hb : d99384 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74550, d99384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74550, d99384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74551 q = 1) (hb : d99385 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74551, d99385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74551, d99385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17995 (p : Pattern) (ha : d74557 p = 1) (hb : d99391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74552 q = 1) (hb : d99386 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74552, d99386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17994 q ha hb
    | true =>
      simp only [d74552, d99386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74553 q = 1) (hb : d99387 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74553, d99387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74553, d99387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74554 q = 1) (hb : d99388 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74554, d99388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74554, d99388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74555 q = 1) (hb : d99389 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74555, d99389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74555, d99389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74556 q = 1) (hb : d99390 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74556, d99390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74556, d99390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74557 q = 1) (hb : d99391 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74557, d99391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74557, d99391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17996 (p : Pattern) (ha : d74563 p = 1) (hb : d99397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74558 q = 1) (hb : d99392 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74558, d99392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17995 q ha hb
    | true =>
      simp only [d74558, d99392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74559 q = 1) (hb : d99393 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74559, d99393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74559, d99393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74560 q = 1) (hb : d99394 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74560, d99394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74560, d99394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74561 q = 1) (hb : d99395 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74561, d99395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74561, d99395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74562 q = 1) (hb : d99396 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74562, d99396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74562, d99396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74563 q = 1) (hb : d99397 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74563, d99397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74563, d99397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17997 (p : Pattern) (ha : d74569 p = 1) (hb : d99403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74564 q = 1) (hb : d99398 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74564, d99398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17996 q ha hb
    | true =>
      simp only [d74564, d99398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74565 q = 1) (hb : d99399 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74565, d99399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74565, d99399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74566 q = 1) (hb : d99400 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74566, d99400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74566, d99400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74567 q = 1) (hb : d99401 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74567, d99401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74567, d99401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74568 q = 1) (hb : d99402 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74568, d99402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74568, d99402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74569 q = 1) (hb : d99403 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74569, d99403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74569, d99403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17998 (p : Pattern) (ha : d74575 p = 1) (hb : d99409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74570 q = 1) (hb : d99404 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74570, d99404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17997 q ha hb
    | true =>
      simp only [d74570, d99404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74571 q = 1) (hb : d99405 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74571, d99405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74571, d99405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74572 q = 1) (hb : d99406 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74572, d99406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74572, d99406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74573 q = 1) (hb : d99407 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74573, d99407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74573, d99407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74574 q = 1) (hb : d99408 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74574, d99408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74574, d99408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74575 q = 1) (hb : d99409 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74575, d99409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74575, d99409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17999 (p : Pattern) (ha : d7302 p = 1) (hb : d74579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d337 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7248 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4371 q = 1) (hb : d7298 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d7298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4371, d7298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7299 q = 1) (hb : d74576 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d7299, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7300 q = 1) (hb : d74577 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7300, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7301 q = 1) (hb : d74578 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7301, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7302 q = 1) (hb : d74579 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7302, d74579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7302, d74579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
end NetHack.Soko22Hazard87
